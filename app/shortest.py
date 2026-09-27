"""规范最短违规执行审计：冻结来源复核，精确求总切换数最小的接受套索。

与 :mod:`app.checker` 的关系
---------------------------
自动机与乘积完全复用 checker 的 ``push_negation`` / ``build_gba`` /
``build_product``（冻结来源复核的规程、公式与初态，不引入第二套语义、
不改写来源复核记录）。本模块只做一件事：在可达**乘积图**（位置 × 否定
GBA 基本集）上精确求「规范最短」接受套索：

- 在所有可达接受套索（前缀 + **非空**闭环，每条边都是乘积图中真实存在
  的切换，闭环在循环内命中**每个**公平集）中，取**总切换数最小**者；
- 同长度时依次按前缀、闭环的**切换标识序列**字典序裁决——求解完全
  确定，可稳定复现；
- 不凭深度回放、不随机采样、不只在原位置图上找环：闭环起点枚举在乘积
  状态上进行，闭环长度在「乘积状态 × 公平集命中掩码（2^k）」展开图上
  以 BFS 精确求得（k ≤ ``MAX_FAIRNESS_SETS`` 才受理，超出即拒绝）。

精确性要点：任一套索 = 初态到某乘积状态 v 的前缀 + 自 v 出发命中全部
公平集后回到 v 的非空闭环，故最小总长 = min_v dist(初态, v) + c(v)。
候选 v 按其到初态距离升序处理，并用「往返各公平集距离之和」作下界
剪枝；对进入精确计算的 v，正向 BFS 求 c(v)（带预算截断），反向 BFS +
逐层取最小切换标识构造字典序最小的前缀与闭环，最后独立重放校验。
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Any, Deque, Dict, List, Optional, Set, Tuple

from .checker import (
    OnTheFlyGBA,
    Product,
    build_gba,
    build_product,
    eval_subformulas_on_lasso,
    push_negation,
)
from .ltl_parser import Node

#: 该审计可处理的公平集上限（子集掩码 2^k 展开，k 不超过此值）
MAX_FAIRNESS_SETS = 6


class FairnessLimitExceeded(Exception):
    """否定 GBA 产生的公平集超过该审计可处理的上限。"""

    def __init__(self, count: int):
        super().__init__(
            f"公平集 {count} 个，超过该审计可处理的上限 {MAX_FAIRNESS_SETS}"
        )
        self.count = count


class ShortestLassoError(Exception):
    """内部不一致（来源结论与冻结重放矛盾，或套索重放校验失败）。"""


@dataclass
class MinimalLasso:
    """与 checker.Violation 同构：前缀 + 非空闭环（末态回到闭环起点）。"""

    prefix_states: List[int]
    prefix_switches: List[str]
    cycle_states: List[int]
    cycle_switches: List[str]


# ------------------------------------------------------------------ 图工具

def _fwd_dist(adj: List[List[int]], sources: List[int]) -> List[int]:
    """多源 BFS 距离；-1 表示不可达。"""
    dist = [-1] * len(adj)
    dq: Deque[int] = deque()
    for s in sources:
        if dist[s] < 0:
            dist[s] = 0
            dq.append(s)
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if dist[w] < 0:
                dist[w] = dist[u] + 1
                dq.append(w)
    return dist


def _adjacency(edges: List[List[Tuple[int, str]]]) -> List[List[int]]:
    return [[w for w, _ in outs] for outs in edges]


def _predecessors(n: int, edges: List[List[Tuple[int, str]]]) -> List[List[int]]:
    pred: List[List[int]] = [[] for _ in range(n)]
    for u, outs in enumerate(edges):
        for w, _sw in outs:
            pred[w].append(u)
    return pred


# ------------------------------------------------------------------ 最短套索

def find_shortest_lasso(
    product: Product,
) -> Tuple[Optional[MinimalLasso], Dict[str, int]]:
    """在可达乘积图上精确求总切换数最小的接受套索。

    返回 (套索或 None, 搜索统计)。公平集超过上限抛
    :class:`FairnessLimitExceeded`。
    """
    P = product
    n = len(P.states)
    stats = {"cycle_searches": 0}
    if n == 0 or not P.initial:
        return None, stats
    k = len(P.fairness)
    if k > MAX_FAIRNESS_SETS:
        raise FairnessLimitExceeded(k)

    mask = [0] * n
    for g, group in enumerate(P.fairness):
        bit = 1 << g
        for v in group:
            mask[v] |= bit

    fadj = _adjacency(P.edges)
    pred = _predecessors(n, P.edges)
    dist = _fwd_dist(fadj, P.initial)  # 初态集合 -> 各乘积状态

    # 下界：闭环必经每个公平集往返 -> c(v) >= max_g(dist(v,F_g)+dist(F_g,v))
    # 任一方向不可达的 v 不可能处在接受闭环上，直接排除。
    lb = [1] * n
    feasible = [dist[v] >= 0 for v in range(n)]
    for group in P.fairness:
        to_g = _fwd_dist(pred, list(group))   # dist(v -> 集合)
        from_g = _fwd_dist(fadj, list(group))  # dist(集合 -> v)
        for v in range(n):
            if to_g[v] < 0 or from_g[v] < 0:
                feasible[v] = False
            elif feasible[v]:
                lb[v] = max(lb[v], to_g[v] + from_g[v])

    order = sorted((v for v in range(n) if feasible[v]), key=lambda v: dist[v])
    best_total: Optional[int] = None
    champion: Optional[MinimalLasso] = None
    champion_key: Tuple[Tuple[str, ...], Tuple[str, ...]] = ((), ())
    for v in order:
        dv = dist[v]
        if best_total is not None and dv >= best_total:
            break  # 闭环至少 1 条边，之后的候选只会更长
        if best_total is not None and dv + lb[v] > best_total:
            continue  # 下界已不可能更优、也不可能持平
        budget = None if best_total is None else best_total - dv
        stats["cycle_searches"] += 1
        c = _cycle_length(P.edges, mask, k, v, budget)
        if c is None:
            continue
        total = dv + c
        if best_total is not None and total > best_total:
            continue
        prefix_states, prefix_seq = _prefix_path(P, pred, dist, v)
        cycle_states, cycle_seq = _cycle_path(P.edges, pred, mask, k, v, c)
        key = (tuple(prefix_seq), tuple(cycle_seq))
        if best_total is None or total < best_total or key < champion_key:
            best_total = total
            champion_key = key
            champion = MinimalLasso(prefix_states, prefix_seq,
                                    cycle_states, cycle_seq)
    return champion, stats


def _cycle_length(
    edges: List[List[Tuple[int, str]]],
    mask: List[int],
    k: int,
    v: int,
    budget: Optional[int],
) -> Optional[int]:
    """v 出发、循环内命中全部公平集的最短非空闭环长度。

    在「乘积状态 × 命中掩码」展开图上 BFS；超过 budget 视为不存在
    （返回 None）。闭环至少一条边：从 v 的后继作为第 1 层种子起步。
    """
    if budget is not None and budget < 1:
        return None
    msize = 1 << k
    full = msize - 1
    n = len(edges)
    target = v * msize + full
    ds = [-1] * (n * msize)
    dq: Deque[int] = deque()
    seed_mask = mask[v]
    for w, _sw in edges[v]:
        node = w * msize + (seed_mask | mask[w])
        if ds[node] < 0:
            ds[node] = 1
            dq.append(node)
    if ds[target] == 1:
        return 1
    while dq:
        node = dq.popleft()
        d = ds[node]
        if budget is not None and d >= budget:
            continue  # 超出预算的层不再展开
        u, m = divmod(node, msize)
        for w, _sw in edges[u]:
            nxt = w * msize + (m | mask[w])
            if ds[nxt] < 0:
                ds[nxt] = d + 1
                if nxt == target:
                    return d + 1
                dq.append(nxt)
    return None


def _cycle_path(
    edges: List[List[Tuple[int, str]]],
    pred: List[List[int]],
    mask: List[int],
    k: int,
    v: int,
    depth: int,
) -> Tuple[List[int], List[str]]:
    """自 v 出发长度为 depth 的接受闭环中，切换标识序列字典序最小者。

    反向 BFS 求得到目标 (v, 满掩码) 的距离后，从 (v, mask[v]) 逐层
    取最小切换标识；再沿选定层回溯出具体乘积状态序列（确定可复现）。
    """
    msize = 1 << k
    full = msize - 1
    n = len(edges)
    dt = [-1] * (n * msize)
    start_target = v * msize + full
    dt[start_target] = 0
    dq: Deque[int] = deque([start_target])
    while dq:
        node = dq.popleft()
        d = dt[node]
        w, mp = divmod(node, msize)
        base = mp & ~mask[w]
        opt = mp & mask[w]
        for u in pred[w]:
            sub = opt
            while True:
                pm = base | sub
                pnode = u * msize + pm
                if dt[pnode] < 0:
                    dt[pnode] = d + 1
                    dq.append(pnode)
                if sub == 0:
                    break
                sub = (sub - 1) & opt

    seq: List[str] = []
    frontier = {v * msize + mask[v]}
    layers = [frontier]
    for t in range(depth):
        best_sw: Optional[str] = None
        nxt: Set[int] = set()
        for node in frontier:
            u, m = divmod(node, msize)
            for w, sw in edges[u]:
                nn = w * msize + (m | mask[w])
                if dt[nn] == depth - t - 1:
                    if best_sw is None or sw < best_sw:
                        best_sw = sw
                        nxt = {nn}
                    elif sw == best_sw:
                        nxt.add(nn)
        assert best_sw is not None  # depth 由 BFS 保证可达
        seq.append(best_sw)
        frontier = nxt
        layers.append(frontier)

    # 回溯具体乘积状态：逐层取能经选定切换到达后继的最小编号前驱
    hnodes = [0] * (depth + 1)
    hnodes[depth] = start_target
    for t in range(depth, 0, -1):
        u, m = divmod(hnodes[t], msize)
        choice: Optional[int] = None
        for pnode in layers[t - 1]:
            pu, pm = divmod(pnode, msize)
            if pm | mask[u] != m:
                continue
            for w, sw in edges[pu]:
                if w == u and sw == seq[t - 1]:
                    if choice is None or pnode < choice:
                        choice = pnode
                    break
        assert choice is not None
        hnodes[t - 1] = choice
    cycle_states = [h // msize for h in hnodes]
    return cycle_states, seq


def _prefix_path(
    P: Product,
    pred: List[List[int]],
    dist: List[int],
    v: int,
) -> Tuple[List[int], List[str]]:
    """初态集合到 v 的最短前缀中，切换标识序列字典序最小者。"""
    depth = dist[v]
    if depth == 0:
        return [v], []
    n = len(P.states)
    d2 = [-1] * n  # 各状态到 v 的距离（反向 BFS）
    d2[v] = 0
    dq: Deque[int] = deque([v])
    while dq:
        x = dq.popleft()
        for u in pred[x]:
            if d2[u] < 0:
                d2[u] = d2[x] + 1
                dq.append(u)

    seq: List[str] = []
    frontier = {s for s in P.initial if d2[s] == depth}
    layers = [frontier]
    for t in range(depth):
        best_sw: Optional[str] = None
        nxt: Set[int] = set()
        for u in frontier:
            for w, sw in P.edges[u]:
                if d2[w] == depth - t - 1:
                    if best_sw is None or sw < best_sw:
                        best_sw = sw
                        nxt = {w}
                    elif sw == best_sw:
                        nxt.add(w)
        assert best_sw is not None
        seq.append(best_sw)
        frontier = nxt
        layers.append(frontier)

    states = [0] * (depth + 1)
    states[depth] = v
    for t in range(depth, 0, -1):
        cur = states[t]
        choice: Optional[int] = None
        for u in layers[t - 1]:
            for w, sw in P.edges[u]:
                if w == cur and sw == seq[t - 1]:
                    if choice is None or u < choice:
                        choice = u
                    break
        assert choice is not None
        states[t - 1] = choice
    return states, seq


# ------------------------------------------------------------------ 重放校验

def replay_validate(product: Product, lasso: MinimalLasso) -> List[str]:
    """独立重放校验：每步切换真实存在、闭环非空且闭合、循环内命中每个
    公平集、前缀始于初态。返回问题列表（空 = 通过）。"""
    problems: List[str] = []
    P = product
    initial = set(P.initial)

    if not lasso.prefix_states:
        problems.append("前缀状态序列为空")
        return problems
    if lasso.prefix_states[0] not in initial:
        problems.append("前缀未始于初态乘积状态")
    if len(lasso.prefix_states) != len(lasso.prefix_switches) + 1:
        problems.append("前缀状态数与切换数不符")
    for i, sw in enumerate(lasso.prefix_switches):
        u, w = lasso.prefix_states[i], lasso.prefix_states[i + 1]
        if (w, sw) not in P.edges[u]:
            problems.append(f"前缀第 {i} 步切换 '{sw}' 在乘积图中不存在")

    if not lasso.cycle_switches:
        problems.append("闭环为空（至少需要一条切换）")
    if len(lasso.cycle_states) != len(lasso.cycle_switches) + 1:
        problems.append("闭环状态数与切换数不符")
    if lasso.cycle_states and lasso.cycle_states[0] != lasso.cycle_states[-1]:
        problems.append("闭环未闭合（末态未回到起点）")
    if (lasso.cycle_states
            and lasso.prefix_states[-1] != lasso.cycle_states[0]):
        problems.append("前缀末端与闭环起点不一致")
    for i, sw in enumerate(lasso.cycle_switches):
        u, w = lasso.cycle_states[i], lasso.cycle_states[i + 1]
        if (w, sw) not in P.edges[u]:
            problems.append(f"闭环第 {i} 步切换 '{sw}' 在乘积图中不存在")

    loop_states = set(lasso.cycle_states[:-1])  # 末态与起点重复，去重
    for g, group in enumerate(P.fairness):
        if not (group & loop_states):
            problems.append(f"公平集 {g} 未在闭环循环内命中")
    return problems


# ------------------------------------------------------------------ 证据

def build_minimal_violation(
    formula_ast: Node,
    gba: OnTheFlyGBA,
    product: Product,
    lasso: MinimalLasso,
) -> Dict[str, Any]:
    """最短套索的逐步证据：位置、切换、命题、子式真值与公平集命中。"""
    m = len(lasso.prefix_switches)
    r = len(lasso.cycle_switches)
    total = m + r
    k = len(product.fairness)
    q_states = lasso.prefix_states[:m] + lasso.cycle_states[:r]
    q_switches = lasso.prefix_switches + lasso.cycle_switches
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
            "fairness_sets_hit": [
                g for g in range(k) if sid in product.fairness[g]
            ],
            "subformula_truth": evidence[i],
            "formula_true_here": evidence[i][formula_str],
            "negation_automaton_formulas": [
                gba.closure.nodes[j].to_str() for j in sorted(ps.ap)
            ],
        })

    coverage: List[Dict[str, Any]] = []
    for g in range(k):
        hits = [i for i in range(m, total)
                if q_states[i] in product.fairness[g]]
        coverage.append({
            "set": g,
            "eventuality": gba.events[g].to_str(),
            "hit_step_indices": hits,
        })

    return {
        "kind": "minimal_lasso",
        "prefix_length": m,
        "cycle_length": r,
        "total_switches": total,
        "loop_start_index": m,
        "selection": (
            "全部可达接受套索中总切换数最小；同长度依次按前缀、闭环的"
            "切换标识序列字典序裁决（确定性求解，可稳定复现）"
        ),
        "steps": steps,
        "fairness_coverage": coverage,
        "note": (
            "前 prefix_length 步为有限前缀；自 loop_start_index 起进入长度 "
            "cycle_length 的非空重复闭环，每条边均为规程中真实声明的切换，"
            "闭环在循环内命中每个公平集（见 fairness_coverage 与各步 "
            "fairness_sets_hit），故为真正的无限违规执行，无法以有限回放"
            "掩盖迟发或永不发生。"
        ),
    }


# ------------------------------------------------------------------ 审计编排

def frozen_spec(spec: Dict[str, Any]) -> Dict[str, Any]:
    """从已校验请求提取可 JSON 持久化的冻结规程（不含 AST 等内部件）。"""
    return {
        "locations": list(spec["locations"]),
        "initial": spec["initial"],
        "switches": [dict(sw) for sw in spec["switches"]],
        "propositions": {
            loc: list(plist) for loc, plist in spec["propositions"].items()
        },
        "formula": spec["formula"],
    }


def run_shortest_audit(
    spec: Dict[str, Any], source_check_id: str
) -> Dict[str, Any]:
    """在冻结规程上重放否定 GBA × 规程乘积，求规范最短违规执行。

    公平集超上限抛 :class:`FairnessLimitExceeded`；与来源结论矛盾或
    重放校验失败抛 :class:`ShortestLassoError`。返回不含编号的审计记录。
    """
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
    k = len(gba.events)
    if k > MAX_FAIRNESS_SETS:
        raise FairnessLimitExceeded(k)

    lasso, search_stats = find_shortest_lasso(product)
    if lasso is None:
        raise ShortestLassoError(
            "来源复核结论为不成立，但在冻结规程的乘积中未复现接受套索"
            "（内部不一致）"
        )
    problems = replay_validate(product, lasso)
    if problems:
        raise ShortestLassoError("最短套索重放校验失败：" + "；".join(problems))

    violation = build_minimal_violation(formula_ast, gba, product, lasso)
    return {
        "kind": "shortest_violation_audit",
        "source_check_id": source_check_id,
        "formula": spec["formula"],
        "initial": spec["initial"],
        "holds": False,
        "spec": frozen_spec(spec),
        "normalization": {
            "negation_nnf": neg_nnf.to_str(),
            "method": (
                "否定公式广义 Büchi 自动机（tableau）× 规程乘积 × "
                "精确最短接受套索（掩码展开 BFS + 切换标识字典序裁决）"
            ),
        },
        "stats": {
            "closure_size": len(gba.closure.nodes),
            "gba_states_reachable": len(gba.seen_aps),
            "fairness_sets": k,
            "product_states": len(product.states),
            "product_edges": sum(len(e) for e in product.edges),
            **search_stats,
        },
        "violation": violation,
    }
