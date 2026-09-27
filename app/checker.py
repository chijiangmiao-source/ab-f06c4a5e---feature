"""在线 LTL 模型检测核心。

算法（显式状态广义 Büchi 乘积 + 接受 SCC，完整判定；无回放深度、无随机采样、
不只检查状态标签）：

1. 将用户公式 φ 规范化为 NNF(¬φ)（否定下压，F/G/U/V 互为对偶）。
2. 取 ¬φ 的 Fischer–Ladkin 闭包（子式、X-迁移式、以及每个成员的互补式），
   枚举全部「局部一致」基本公式集（elementary/Hintikka 集）作为
   *否定公式的广义 Büchi 自动机（GBA）* 状态；X 公式决定后继约束，
   每个 F/U 事件性子式对应一个公平集。
3. 与规程 Kripke 结构做乘积（位置 × GBA 状态，沿声明的有向切换迁移，
   位置标签须与自动机状态的字面量一致），只保留初态可达部分。
4. 对可达乘积图求 SCC；存在被所有公平集命中的可达非平凡 SCC，
   当且仅当存在满足 ¬φ 的无限执行（φ 被违反），并在其中构造
   「前缀 + 重复闭环」套索。
5. 证据：在套索周期序列上以最小/最大不动点迭代求 φ 全部子式的逐点真值。
"""

from __future__ import annotations

import sys
from collections import deque
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple

from .ltl_parser import Node, subformulas

# 乘积图 SCC 为显式递归，放开 Python 递归深度
sys.setrecursionlimit(1_000_000)

TRUE = Node("atom", p="true")
FALSE = Node("atom", p="false")


# ------------------------------------------------------------------ 规范化

def push_negation(node: Node, neg: bool = False) -> Node:
    """NNF(node)；neg=True 时为 NNF(¬node)，否定只停留在字面量上。"""
    t = node.type
    if t == "atom":
        if node.p == "true":
            return FALSE if neg else TRUE
        if node.p == "false":
            return TRUE if neg else FALSE
        return Node("not", node) if neg else node
    if t == "not":
        return push_negation(node.a, not neg)
    if t == "and":
        return Node(
            "or" if neg else "and",
            push_negation(node.a, neg),
            push_negation(node.b, neg),
        )
    if t == "or":
        return Node(
            "and" if neg else "or",
            push_negation(node.a, neg),
            push_negation(node.b, neg),
        )
    if t == "next":
        # ¬X p ≡ X ¬p
        return Node("next", push_negation(node.a, neg))
    if t == "eventually":  # ¬F p ≡ G ¬p
        if neg:
            return Node("always", push_negation(node.a, True))
        return Node("eventually", push_negation(node.a))
    if t == "always":  # ¬G p ≡ F ¬p
        if neg:
            return Node("eventually", push_negation(node.a, True))
        return Node("always", push_negation(node.a))
    if t == "until":  # ¬(a U b) ≡ ¬a V ¬b
        if neg:
            return Node(
                "release",
                push_negation(node.a, True),
                push_negation(node.b, True),
            )
        return Node("until", push_negation(node.a), push_negation(node.b))
    if t == "release":  # ¬(a V b) ≡ ¬a U ¬b
        if neg:
            return Node(
                "until",
                push_negation(node.a, True),
                push_negation(node.b, True),
            )
        return Node("release", push_negation(node.a), push_negation(node.b))
    raise ValueError(f"未知节点类型 {t}")


# ------------------------------------------------------------------ 闭包

_TEMPORAL = ("eventually", "always", "until", "release")


@dataclass
class Closure:
    root: Node
    nodes: List[Node]
    index: Dict[Node, int]
    events: List[Node]                       # F / U 子式
    event_group: Dict[int, int]              # 闭包下标 -> 公平集编号
    x_node_of: Dict[int, int]                # 不动点时序式下标 -> 其 X 迁移式下标


def _add_with_subs(node: Node, seen: Set[Node], out: List[Node]) -> bool:
    grew = False
    for s in subformulas(node):
        if s not in seen:
            seen.add(s)
            out.append(s)
            grew = True
    return grew


def build_closure(root: Node) -> Closure:
    seen: Set[Node] = set()
    gathered: List[Node] = []
    _add_with_subs(root, seen, gathered)

    # 不动点闭包：每个不动点时序式加入其 X 迁移式 Xψ
    while True:
        grew = False
        for n in list(gathered):
            if n.type in _TEMPORAL:
                grew |= _add_with_subs(Node("next", n), seen, gathered)
        if not grew:
            break

    # 拓扑排序：规则依赖的位必须排在前面
    #   - 合取/析取/U/V/F/G：直接子式在前
    #   - 不动点时序式：其 X 迁移式在前
    deps: Dict[Node, Set[Node]] = {}
    for n in gathered:
        d: Set[Node] = set()
        t = n.type
        if t == "next":
            # X 迁移节点在局部一致性中是叶子（不读子式位），
            # 其子式就是 ψ 自身，不能反向构成依赖环
            pass
        elif t in ("not", "eventually", "always"):
            if n.a in seen:
                d.add(n.a)
        elif t in ("and", "or", "until", "release"):
            d.add(n.a)
            d.add(n.b)
        if t in _TEMPORAL:
            d.add(Node("next", n))
        deps[n] = d

    ordered: List[Node] = []
    temp_mark: Set[Node] = set()
    done: Set[Node] = set()

    def visit(n: Node) -> None:
        if n in done:
            return
        if n in temp_mark:  # pragma: no cover - 子式依赖无环
            raise ValueError("闭包依赖出现循环")
        temp_mark.add(n)
        for d in sorted(deps[n], key=lambda x: x.to_str()):
            visit(d)
        temp_mark.discard(n)
        done.add(n)
        ordered.append(n)

    for n in sorted(gathered, key=lambda x: x.to_str()):
        visit(n)

    index = {n: i for i, n in enumerate(ordered)}
    events = [n for n in ordered if n.type in ("eventually", "until")]
    event_group = {index[n]: k for k, n in enumerate(events)}
    x_node_of: Dict[int, int] = {
        index[n]: index[Node("next", n)]
        for n in ordered
        if n.type in _TEMPORAL
    }

    return Closure(
        root=root,
        nodes=ordered,
        index=index,
        events=events,
        event_group=event_group,
        x_node_of=x_node_of,
    )


# --------------------------------------- GBA：按需展开的 tableau 自动机

@dataclass
class OnTheFlyGBA:
    """否定公式的广义 Büchi 自动机，按需展开。

    不预枚举全部 2^闭包 基本集、不建 |A|² 迁移表；只在乘积遍历时，
    按位置标签与 X 后继约束生成真正可达的基本公式集。基本集定义、
    X 迁移规则与公平集定义与经典 tableau 完全一致，因此接受语言不变。
    """

    closure: Closure
    root_i: int
    events: List[Node]
    seen_aps: Set[FrozenSet[int]] = field(default_factory=set)

    def __post_init__(self):
        cl = self.closure
        m = len(cl.nodes)

        def child_of(i: int) -> Tuple[int, ...]:
            n = cl.nodes[i]
            if n.type in ("not", "next", "eventually", "always"):
                return (cl.index[n.a],)
            if n.type in ("and", "or", "until", "release"):
                return (cl.index[n.a], cl.index[n.b])
            return ()

        self._m = m
        self._child = child_of
        # 闭包内同时出现的字面量互补对（恰取其一）
        lit_pos: Dict[str, int] = {}
        lit_neg: Dict[str, int] = {}
        for i, n in enumerate(cl.nodes):
            if n.type == "atom" and n.p not in ("true", "false"):
                lit_pos[n.p] = i
            elif n.type == "not" and n.a.type == "atom":
                lit_neg[n.a.p] = i
        self._mate: Dict[int, int] = {}
        for name, pi in lit_pos.items():
            if name in lit_neg:
                self._mate[pi] = lit_neg[name]
                self._mate[lit_neg[name]] = pi
        # 每个 Xψ 闭包成员 -> ψ 下标（后继约束）
        self._x_requirements = [
            (i, child_of(i)[0])
            for i, n in enumerate(cl.nodes)
            if n.type == "next"
        ]
        self._enum_cache: Dict[
            Tuple[FrozenSet[Tuple[int, bool]], FrozenSet[int]],
            Tuple[FrozenSet[int], ...],
        ] = {}

    # -------------------------------------------------- 基本集局部一致性
    def _consistent(self, mask: int, i: int, present: bool) -> bool:
        n = self.closure.nodes[i]
        t = n.type
        bit = lambda j: bool((mask >> j) & 1)
        if t == "atom":
            if n.p == "true":
                return present is True
            if n.p == "false":
                return present is False
            return True
        if t == "not":
            return True
        ch = self._child(i)
        if t == "and":
            return present == (bit(ch[0]) and bit(ch[1]))
        if t == "or":
            return present == (bit(ch[0]) or bit(ch[1]))
        if t == "next":
            return True
        xi = self.closure.x_node_of[i]
        if t == "eventually":
            return present == (bit(ch[0]) or bit(xi))
        if t == "always":
            return present == (bit(ch[0]) and bit(xi))
        if t == "until":
            return present == (bit(ch[1]) or (bit(ch[0]) and bit(xi)))
        if t == "release":
            return present == (bit(ch[1]) and (bit(ch[0]) or bit(xi)))
        raise ValueError(t)

    def _enumerate(
        self,
        fixed: Dict[int, bool],
        required: FrozenSet[int] = frozenset(),
    ) -> Tuple[FrozenSet[int], ...]:
        """枚举满足 fixed 位约束、含 required 全部成员的所有基本集。"""
        key = (frozenset(fixed.items()), required)
        cached = self._enum_cache.get(key)
        if cached is not None:
            return cached

        results: List[FrozenSet[int]] = []

        def dfs(pos: int, mask: int) -> None:
            if pos == self._m:
                present_set = frozenset(
                    j for j in range(self._m) if (mask >> j) & 1
                )
                if required <= present_set:
                    results.append(present_set)
                return
            mate = self._mate.get(pos)
            if pos in fixed:
                present = fixed[pos]
                # 与互补位的已定值冲突 -> 剪枝
                if mate is not None and mate < pos:
                    if present == bool((mask >> mate) & 1):
                        return
                if self._consistent(mask, pos, present):
                    dfs(pos + 1, mask | (int(present) << pos))
                return
            if mate is not None and mate < pos:
                choices = (not bool((mask >> mate) & 1),)  # 恰取其一
            else:
                choices = (True, False)
            for present in choices:
                if self._consistent(mask, pos, present):
                    dfs(pos + 1, mask | (int(present) << pos))

        dfs(0, 0)
        out = tuple(results)
        self._enum_cache[key] = out
        self.seen_aps.update(out)
        return out

    # -------------------------------------------------- 标签 / 初始 / 迁移
    def label_fixed(self, labels: Set[str]) -> Dict[int, bool]:
        """位置命题标签对字面量位的固定约束。"""
        fixed: Dict[int, bool] = {}
        for i, n in enumerate(self.closure.nodes):
            lit = _literal(n)
            if lit is None:
                continue
            name, positive = lit
            fixed[i] = (name in labels) if positive else (name not in labels)
        return fixed

    def initial_states(
        self, labels: Set[str]
    ) -> Tuple[FrozenSet[int], ...]:
        return self._enumerate(
            self.label_fixed(labels), frozenset([self.root_i])
        )

    def successors(
        self, ap: FrozenSet[int], labels: Set[str]
    ) -> Tuple[FrozenSet[int], ...]:
        fixed = self.label_fixed(labels)
        for xi, child in self._x_requirements:
            # ψ ∈ A' ⇔ Xψ ∈ A；与标签约束冲突时该迁移无后继，
            # 绝不能覆盖标签固定值
            need = xi in ap
            if child in fixed and fixed[child] != need:
                return ()
            fixed[child] = need
        return self._enumerate(fixed)

    def accepting_groups(self, ap: FrozenSet[int]) -> Set[int]:
        groups: Set[int] = set()
        for g, ev in enumerate(self.events):
            ei = self.closure.index[ev]
            witness = self.closure.index[
                ev.a if ev.type == "eventually" else ev.b
            ]
            if witness in ap or ei not in ap:
                groups.add(g)
        return groups


def build_gba(neg_nnf: Node) -> OnTheFlyGBA:
    cl = build_closure(neg_nnf)
    return OnTheFlyGBA(
        closure=cl,
        root_i=cl.index[neg_nnf],
        events=list(cl.events),
    )


def _literal(node: Node) -> Optional[Tuple[str, bool]]:
    """字面量 -> (命题名, 是否正极性)；true/false 与复合式返回 None。"""
    if node.type == "atom":
        if node.p in ("true", "false"):
            return None
        return node.p, True
    if node.type == "not" and node.a.type == "atom":
        return node.a.p, False
    return None


# ------------------------------------------------------------------ 乘积

@dataclass(frozen=True)
class PState:
    loc: str
    ap: FrozenSet[int]


@dataclass
class Product:
    states: List[PState]
    edges: List[List[Tuple[int, str]]]
    initial: List[int]
    fairness: List[Set[int]]
    loc_labels: Dict[str, Set[str]]


def build_product(
    gba: OnTheFlyGBA,
    locations: List[str],
    initial_loc: str,
    outgoing: Dict[str, List[Dict[str, str]]],
    propositions: Dict[str, List[str]],
) -> Product:
    labels = {loc: set(plist) for loc, plist in propositions.items()}

    states: List[PState] = []
    sid: Dict[PState, int] = {}

    def intern(ps: PState) -> int:
        v = sid.get(ps)
        if v is None:
            v = len(states)
            sid[ps] = v
            states.append(ps)
        return v

    queue: deque[int] = deque()
    root_aps: List[FrozenSet[int]] = []
    for ap in gba.initial_states(labels[initial_loc]):
        root_aps.append(ap)
        queue.append(intern(PState(initial_loc, ap)))
    root_ap_set = set(root_aps)

    edges: List[List[Tuple[int, str]]] = []

    def pad(v: int) -> None:
        while len(edges) <= v:
            edges.append([])

    while queue:
        u = queue.popleft()
        pad(u)
        ps = states[u]
        for sw in outgoing[ps.loc]:
            dst = sw["target"]
            for ap2 in gba.successors(ps.ap, labels[dst]):
                nxt = PState(dst, ap2)
                existed = nxt in sid
                v = intern(nxt)
                pad(v)
                edges[u].append((v, sw["id"]))
                if not existed:
                    queue.append(v)

    n_fair = len(gba.events)
    fairness: List[Set[int]] = [set() for _ in range(n_fair)]
    for v, ps in enumerate(states):
        for g in gba.accepting_groups(ps.ap):
            fairness[g].add(v)

    return Product(
        states=states,
        edges=edges,
        initial=[
            v for v, p in enumerate(states)
            if p.loc == initial_loc and p.ap in root_ap_set
        ],
        fairness=fairness,
        loc_labels=labels,
    )


# ------------------------------------------------------------------ 搜索

def tarjan_scc(n: int, edges: List[List[Tuple[int, str]]]) -> List[List[int]]:
    index_at: Dict[int, int] = {}
    low: Dict[int, int] = {}
    onstack: Set[int] = set()
    stack: List[int] = []
    counter = 0
    sccs: List[List[int]] = []

    def strong(v: int) -> None:
        nonlocal counter
        index_at[v] = low[v] = counter
        counter += 1
        stack.append(v)
        onstack.add(v)
        for w, _ in edges[v]:
            if w not in index_at:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], index_at[w])
        if low[v] == index_at[v]:
            comp: List[int] = []
            while True:
                w = stack.pop()
                onstack.discard(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)

    for v in range(n):
        if v not in index_at:
            strong(v)
    return sccs


def _bfs(
    edges: List[List[Tuple[int, str]]],
    starts: List[int],
    goal: Callable[[int], bool],
) -> Optional[Tuple[List[int], List[str]]]:
    """starts 任一点 -> 首个满足 goal 的点的最短路；起点不带 prev。"""
    prev: Dict[int, Tuple[int, str]] = {}
    seen = set(starts)
    dq: deque[int] = deque(starts)
    target: Optional[int] = None
    while dq:
        v = dq.popleft()
        if goal(v):
            target = v
            break
        for w, sw in edges[v]:
            if w not in seen:
                seen.add(w)
                prev[w] = (v, sw)
                dq.append(w)
    if target is None:
        return None
    verts, sws = [target], []
    while verts[-1] in prev:
        pv, sw = prev[verts[-1]]
        sws.append(sw)
        verts.append(pv)
    verts.reverse()
    sws.reverse()
    return verts, sws


def _bfs_in(
    edges: List[List[Tuple[int, str]]],
    src: int,
    dst: int,
    allowed: Set[int],
) -> Optional[Tuple[List[int], List[str]]]:
    """allowed 子图内 src -> dst 最短路。"""
    if src == dst:
        return [src], []
    prev: Dict[int, Tuple[int, str]] = {src: (src, "")}
    dq: deque[int] = deque([src])
    while dq:
        v = dq.popleft()
        for w, sw in edges[v]:
            if w not in allowed or w in prev:
                continue
            prev[w] = (v, sw)
            if w == dst:
                verts, sws = [w], []
                while verts[-1] != src:
                    pv, ps = prev[verts[-1]]
                    sws.append(ps)
                    verts.append(pv)
                verts.reverse()
                sws.reverse()
                return verts, sws
            dq.append(w)
    return None


def _bfs_cycle_back(
    edges: List[List[Tuple[int, str]]],
    src: int,
    dst: int,
    allowed: Set[int],
) -> Optional[Tuple[List[int], List[str]]]:
    """allowed 子图内 src -> dst 的最短非平凡路径（至少一条边）。"""
    if src != dst:
        return _bfs_in(edges, src, dst, allowed)
    # src == dst：从 src 的后继出发找回 src 的路径（禁止零步空走）
    best: Optional[Tuple[List[int], List[str]]] = None
    for w, sw in edges[src]:
        if w not in allowed:
            continue
        if w == src:
            return [src, src], [sw]  # 自环，最短
        seg = _bfs_in(edges, w, src, allowed)
        if seg is not None:
            cand = ([src] + seg[0], [sw] + seg[1])
            if best is None or len(cand[0]) < len(best[0]):
                best = cand
    return best


@dataclass
class Violation:
    prefix_states: List[int]
    prefix_switches: List[str]
    cycle_states: List[int]
    cycle_switches: List[str]


def find_violation(product: Product) -> Optional[Violation]:
    P = product
    n = len(P.states)
    if n == 0 or not P.initial:
        return None
    for comp in tarjan_scc(n, P.edges):
        cset = set(comp)
        self_loop = any(w == v for v in comp for w, _ in P.edges[v])
        if len(comp) == 1 and not self_loop:
            continue  # 平凡 SCC 不构成环
        if not all(group & cset for group in P.fairness):
            continue  # 广义 Büchi：每个公平集都要在环上出现

        pref = _bfs(P.edges, P.initial, lambda v: v in cset)
        if pref is None:
            continue
        prefix_states, prefix_switches = pref
        v0 = prefix_states[-1]

        # 在 SCC 内选取各公平集见证点（尽量去重），依次行走并回到 v0，
        # 拼成被全部公平集无限次命中的闭合行走。
        witnesses: List[int] = []
        used: Set[int] = set()
        for group in P.fairness:
            pick = next((x for x in group & cset if x not in used), None)
            if pick is None:
                pick = next(iter(group & cset))
            used.add(pick)
            witnesses.append(pick)

        cyc_verts: List[int] = [v0]
        cyc_switches: List[str] = []
        cur = v0
        ok = True
        for wstate in witnesses:
            seg = _bfs_in(P.edges, cur, wstate, cset)
            if seg is None:
                ok = False
                break
            cyc_verts.extend(seg[0][1:])
            cyc_switches.extend(seg[1])
            cur = wstate
        # 回到 v0，且必须至少经过一条边（公平集为空或单点自环 SCC 时
        # 不能退化为零长空走）
        if ok:
            back = _bfs_cycle_back(P.edges, cur, v0, cset)
            if back is None:
                ok = False
            else:
                cyc_verts.extend(back[0][1:])
                cyc_switches.extend(back[1])
        if ok and cyc_switches:
            return Violation(prefix_states, prefix_switches,
                             cyc_verts, cyc_switches)
    return None


# ------------------------------------------ 套索上的子式真值（不动点迭代）

def eval_subformulas_on_lasso(
    formula_ast: Node,
    labels: List[Set[str]],
    next_of: List[int],
) -> List[Dict[str, bool]]:
    """周期序列上求每个子式逐点真值。

    按子式递归的 Emerson–Lei 嵌套不动点（F/U 取最小、G/V 取最大），
    每轮在 n 个位置的布尔格上至少增/减一个元素，n 轮内必达不动点，
    对任意嵌套深度（含 FG、GF 等交替式）精确。
    """
    subs = subformulas(formula_ast)
    n = len(labels)
    universe = set(range(n))
    cache: Dict[Node, Set[int]] = {}

    def pre(s: Set[int]) -> Set[int]:
        return {i for i in universe if next_of[i] in s}

    def ev(node: Node) -> Set[int]:
        if node in cache:
            return cache[node]
        t = node.type
        if t == "atom":
            if node.p == "true":
                r = set(universe)
            elif node.p == "false":
                r = set()
            else:
                r = {i for i in universe if node.p in labels[i]}
        elif t == "not":
            r = universe - ev(node.a)
        elif t == "and":
            r = ev(node.a) & ev(node.b)
        elif t == "or":
            r = ev(node.a) | ev(node.b)
        elif t == "next":
            r = pre(ev(node.a))
        elif t == "eventually":  # μZ. A ∪ XZ
            a = ev(node.a)
            z: Set[int] = set()
            while True:
                nz = a | pre(z)
                if nz == z:
                    break
                z = nz
            r = z
        elif t == "until":  # μZ. B ∪ (A ∩ XZ)
            a, b = ev(node.a), ev(node.b)
            z = set()
            while True:
                nz = b | (a & pre(z))
                if nz == z:
                    break
                z = nz
            r = z
        elif t == "always":  # νZ. A ∩ XZ
            a = ev(node.a)
            z = set(universe)
            while True:
                nz = a & pre(z)
                if nz == z:
                    break
                z = nz
            r = z
        elif t == "release":  # νZ. B ∩ (A ∪ XZ)
            a, b = ev(node.a), ev(node.b)
            z = set(universe)
            while True:
                nz = b & (a | pre(z))
                if nz == z:
                    break
                z = nz
            r = z
        else:
            raise ValueError(t)
        cache[node] = r
        return r

    for node in subs:
        ev(node)

    out: List[Dict[str, bool]] = [dict() for _ in range(n)]
    for i in range(n):
        for node in subs:
            out[i][node.to_str()] = i in cache[node]
    return out


# ------------------------------------------------------------------ 主流程

@dataclass
class CheckResult:
    holds: bool
    violation: Optional[Dict[str, Any]] = None
    stats: Dict[str, int] = field(default_factory=dict)


def check(spec: Dict[str, Any]) -> CheckResult:
    formula_ast: Node = spec["formula_ast"]
    neg_nnf = push_negation(formula_ast, neg=True)
    gba = build_gba(neg_nnf)
    product = build_product(
        gba,
        spec["locations"],
        spec["initial"],
        spec["outgoing"],
        spec["propositions"],
    )
    viol = find_violation(product)

    stats = {
        "closure_size": len(gba.closure.nodes),
        "gba_states_reachable": len(gba.seen_aps),
        "fairness_sets": len(gba.events),
        "product_states": len(product.states),
        "product_edges": sum(len(e) for e in product.edges),
    }
    if viol is None:
        return CheckResult(holds=True, stats=stats)

    m = len(viol.prefix_switches)
    r = len(viol.cycle_switches)
    total = m + r
    q_states = viol.prefix_states[:m] + viol.cycle_states[:r]
    q_switches = viol.prefix_switches + viol.cycle_switches
    next_of = list(range(1, total)) + [m]

    labels = [product.loc_labels[product.states[s].loc] for s in q_states]
    evidence = eval_subformulas_on_lasso(formula_ast, labels, next_of)
    formula_str = formula_ast.to_str()

    steps: List[Dict[str, Any]] = []
    for i, sid in enumerate(q_states):
        ps = product.states[sid]
        steps.append({
            "index": i,
            "location": ps.loc,
            "switch_taken": q_switches[i],
            "propositions": sorted(product.loc_labels[ps.loc]),
            "subformula_truth": evidence[i],
            "formula_true_here": evidence[i][formula_str],
            "negation_automaton_formulas": [
                gba.closure.nodes[j].to_str()
                for j in sorted(ps.ap)
            ],
        })

    return CheckResult(
        holds=False,
        violation={
            "kind": "lasso",
            "prefix_length": m,
            "cycle_length": r,
            "loop_start_index": m,
            "steps": steps,
            "note": (
                "前 prefix_length 步为有限前缀；自 loop_start_index 起进入长度 "
                "cycle_length 的重复闭环，闭环被全部公平集无限次命中，"
                "故为真正的无限执行，无法以有限回放掩盖迟发或永不发生。"
            ),
        },
        stats=stats,
    )
