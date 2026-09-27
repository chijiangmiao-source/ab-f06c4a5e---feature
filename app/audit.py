"""规范最短违规执行审计。

对已判定不成立的复核，在**冻结的来源规程、公式与初态**上重新使用现有
否定公式 GBA 与规程乘积（:mod:`app.checker` 的同一批构造函数），精确求解
**总切换数最小**的可达接受套索（有限前缀 + 非空闭环）：

- 公平集不超过 :data:`MAX_FAIRNESS_SETS` 个时精确求解：把公平集命中情况
  展开为 2^k 掩码层，在**乘积图**（位置 × GBA 基本集，而非原位置图）上
  逐候选入口求最短覆盖闭环；以已有有效套索长度为上界做分支限界。
  不是深度截断回放、不是随机采样，也不只在原位置图上找环。
- 同长度时依次按前缀、闭环的切换标识序列字典序裁决；再按乘积状态签名
  兜底，保证结果唯一、可稳定复现。
- 闭环非空、每条边真实存在、闭环内命中每个公平集；产出前独立重放验证，
  证据含每步位置、切换与公平集命中。
"""

from __future__ import annotations

import heapq
import itertools
from collections import deque
from dataclasses import dataclass
from typing import Any, Deque, Dict, List, Optional, Set, Tuple

from .checker import (
    Product,
    build_gba,
    build_product,
    push_negation,
    tarjan_scc,
)

#: 该审计可处理的公平集上限（命中情况按 2^k 掩码展开）
MAX_FAIRNESS_SETS = 6


class FairnessLimitExceeded(Exception):
    """公平集数量超过审计可处理上限；调用方须明确拒绝且不新增审计。"""

    def __init__(self, count: int):
        super().__init__(
            f"公平集数量 {count} 超过该审计可处理上限 {MAX_FAIRNESS_SETS}"
        )
        self.count = count


class AuditInvariantError(Exception):
    """求解或独立重放验证发现内部不一致（正常输入下不应发生）。"""


@dataclass
class CanonicalLasso:
    """规范最短套索：prefix_states/switches 为前缀，cycle_* 为非空闭环。"""

    prefix_states: List[int]      # m+1 个，末态即闭环入口
    prefix_switches: List[str]    # m 条
    cycle_states: List[int]       # r+1 个，首尾相同
    cycle_switches: List[str]     # r 条，r >= 1
    candidate_entries: int = 0    # 达到最小总长度的闭环入口数

    @property
    def total(self) -> int:
        return len(self.prefix_switches) + len(self.cycle_switches)


# ------------------------------------------------------------------ 工具

def _state_sig(product: Product, sid: int) -> Tuple[str, Tuple[int, ...]]:
    """乘积状态签名（位置, 排序后的闭包下标），用于确定性兜底裁决。"""
    ps = product.states[sid]
    return (ps.loc, tuple(sorted(ps.ap)))


def _bfs_distances(
    edges: List[List[Tuple[int, str]]], starts: List[int]
) -> Dict[int, int]:
    dist = {s: 0 for s in starts}
    dq: Deque[int] = deque(starts)
    while dq:
        v = dq.popleft()
        for w, _ in edges[v]:
            if w not in dist:
                dist[w] = dist[v] + 1
                dq.append(w)
    return dist


def _accepting_sccs(
    product: Product, fair_mask: List[int], full: int
) -> Dict[int, Set[int]]:
    """状态 -> 所在接受 SCC 的顶点集（非平凡且公平集全覆盖的 SCC）。

    任何覆盖闭环都完整落在某个 SCC 内；该 SCC 必须命中全部公平集，
    否则闭环无从覆盖。反过来，接受 SCC 内任意入口都存在覆盖闭环。
    """
    allowed_of: Dict[int, Set[int]] = {}
    for comp in tarjan_scc(len(product.states), product.edges):
        nontrivial = len(comp) > 1 or any(
            w == v for v in comp for w, _ in product.edges[v]
        )
        if not nontrivial:
            continue
        union = 0
        for v in comp:
            union |= fair_mask[v]
        if union != full:
            continue
        cset = set(comp)
        for v in comp:
            allowed_of[v] = cset
    return allowed_of


# ------------------------------------------------------------------ 长度阶段

def _min_loop_len(
    edges: List[List[Tuple[int, str]]],
    fair_mask: List[int],
    full: int,
    start: int,
    allowed: Set[int],
    cap: int,
) -> Optional[int]:
    """从 start 出发、覆盖全部公平集的最短非空闭环长度（> cap 时返回 None）。

    在 (乘积状态, 命中掩码) 展开图上 BFS；首步强制一条边，保证闭环非空。
    ``cap`` 是由已有有效套索给出的分支限界上界（剪枝不损精确性，
    不是深度截断）。
    """
    start_mask = fair_mask[start]
    visited: Set[Tuple[int, int]] = set()
    dq: Deque[Tuple[int, int, int]] = deque()
    for w, _ in edges[start]:
        if w not in allowed:
            continue
        m = start_mask | fair_mask[w]
        if w == start and m == full:
            return 1
        state = (w, m)
        if state not in visited:
            visited.add(state)
            dq.append((w, m, 1))
    while dq:
        v, m, d = dq.popleft()
        if d >= cap:
            continue
        nd = d + 1
        for w, _ in edges[v]:
            if w not in allowed:
                continue
            m2 = m | fair_mask[w]
            if w == start and m2 == full:
                return nd  # BFS 首次命中即最短
            state = (w, m2)
            if state not in visited:
                visited.add(state)
                dq.append((w, m2, nd))
    return None


# ------------------------------------------------------------------ 序列阶段

def _best_prefixes(
    product: Product,
) -> Tuple[
    Dict[int, Tuple[int, Tuple[str, ...], Tuple[Any, ...]]],
    Dict[int, Tuple[int, str]],
]:
    """到每个乘积状态的最优前缀：键 (距离, 切换序列, 状态签名序列)。

    Dijkstra 的优先级是全序且关于追边单调，故每个状态首次弹出即最优；
    序列裁决保证同一入口的前缀选择唯一、可稳定复现。
    """
    sigs = [_state_sig(product, v) for v in range(len(product.states))]
    best: Dict[int, Tuple[int, Tuple[str, ...], Tuple[Any, ...]]] = {}
    pred: Dict[int, Tuple[int, str]] = {}
    heap: List[Tuple[Any, int, int]] = []
    counter = itertools.count()
    for v in product.initial:
        key = (0, (), (sigs[v],))
        if v not in best or key < best[v]:
            best[v] = key
            heapq.heappush(heap, (key, next(counter), v))
    while heap:
        (d, seq, ss), _, v = heapq.heappop(heap)
        if (d, seq, ss) != best[v]:
            continue
        for w, sw in product.edges[v]:
            nkey = (d + 1, seq + (sw,), ss + (sigs[w],))
            if w not in best or nkey < best[w]:
                best[w] = nkey
                pred[w] = (v, sw)
                heapq.heappush(heap, (nkey, next(counter), w))
    return best, pred


def _best_loop(
    product: Product,
    fair_mask: List[int],
    full: int,
    start: int,
    allowed: Set[int],
    cap: int,
) -> Optional[Tuple[Tuple[str, ...], Tuple[Any, ...], List[int], List[str]]]:
    """从 start 的最优覆盖闭环：键 (长度, 切换序列, 状态签名序列)。

    返回 (切换序列, 签名序列, 闭环状态序列, 闭环切换序列)；闭环非空
    （首步强制一条边），长度不超过 cap。找不到返回 None。
    """
    sigs = [_state_sig(product, v) for v in range(len(product.states))]
    start_mask = fair_mask[start]
    best: Dict[Tuple[int, int], Tuple[int, Tuple[str, ...], Tuple[Any, ...]]] = {}
    pred: Dict[Tuple[int, int], Tuple[Optional[Tuple[int, int]], str]] = {}
    heap: List[Tuple[Any, int, Tuple[int, int]]] = []
    counter = itertools.count()
    for w, sw in product.edges[start]:
        if w not in allowed:
            continue
        m = start_mask | fair_mask[w]
        key = (1, (sw,), (sigs[start], sigs[w]))
        state = (w, m)
        if state not in best or key < best[state]:
            best[state] = key
            pred[state] = (None, sw)
            heapq.heappush(heap, (key, next(counter), state))
    while heap:
        (d, seq, ss), _, state = heapq.heappop(heap)
        if (d, seq, ss) != best[state]:
            continue
        v, m = state
        if v == start and m == full:
            # 首次弹出即最优；回溯出完整闭环
            verts: List[int] = []
            sws: List[str] = []
            key2: Optional[Tuple[int, int]] = state
            while key2 is not None:
                pk, sw = pred[key2]
                sws.append(sw)
                verts.append(key2[0])
                key2 = pk
            verts.reverse()
            sws.reverse()
            cycle_states = [start] + verts
            return seq, ss, cycle_states, sws
        if d >= cap:
            continue
        for w, sw in product.edges[v]:
            if w not in allowed:
                continue
            m2 = m | fair_mask[w]
            nkey = (d + 1, seq + (sw,), ss + (sigs[w],))
            nstate = (w, m2)
            if nstate not in best or nkey < best[nstate]:
                best[nstate] = nkey
                pred[nstate] = (state, sw)
                heapq.heappush(heap, (nkey, next(counter), nstate))
    return None


# ------------------------------------------------------------------ 主求解

def find_canonical_lasso(
    product: Product, original_total: Optional[int] = None
) -> CanonicalLasso:
    """在乘积图上精确求总切换数最小的可达接受套索。

    长度阶段：入口按 (前缀距离, 状态编号) 确定序处理，逐入口在
    (状态, 命中掩码) 展开图上求最短覆盖闭环，以上界分支限界；
    序列阶段：同长度候选间依次按前缀、闭环切换标识序列字典序裁决，
    乘积状态签名兜底，结果唯一、可稳定复现。
    """
    n = len(product.states)
    k = len(product.fairness)
    full = (1 << k) - 1
    fair_mask = [0] * n
    for g, group in enumerate(product.fairness):
        for v in group:
            fair_mask[v] |= 1 << g

    d0 = _bfs_distances(product.edges, product.initial)
    allowed_of = _accepting_sccs(product, fair_mask, full)
    # 任一覆盖闭环长度 <= n * 2^k（展开图状态数），前缀 <= n-1
    fallback = n * (1 << k) + n + 1

    def collect(bound: int) -> Tuple[int, List[int]]:
        best = bound
        cands: List[int] = []
        for dv, v in sorted((d0[v], v) for v in allowed_of):
            if dv >= best:
                continue
            L = _min_loop_len(
                product.edges, fair_mask, full, v, allowed_of[v], best - dv
            )
            if L is None:
                continue
            total = dv + L
            if total < best:
                best = total
                cands = [v]
            elif total == best:
                cands.append(v)
        return best, cands

    if original_total is not None:
        # 来源复核的任意套索是有效上界（同一冻结规格、同一乘积）
        best, candidates = collect(original_total)
        if not candidates:  # 记录异常时的兜底：改用展开图规模上界重试
            best, candidates = collect(fallback)
    else:
        best, candidates = collect(fallback)
    if not candidates:
        raise AuditInvariantError("来源判定不成立，但未找到可达接受套索")

    prefix_key, prefix_pred = _best_prefixes(product)
    chosen: Optional[Tuple[Any, ...]] = None
    for v in candidates:
        dv, pseq, psigs = prefix_key[v]
        loop = _best_loop(
            product, fair_mask, full, v, allowed_of[v], best - dv
        )
        if loop is None:
            raise AuditInvariantError("长度与序列阶段结果不一致")
        lseq, lsigs, cyc_states, cyc_switches = loop
        key = (pseq, lseq, psigs, lsigs)
        if chosen is None or key < chosen[0]:
            chosen = (key, v, cyc_states, cyc_switches)
    assert chosen is not None
    _, entry, cycle_states, cycle_switches = chosen

    pref_states = [entry]
    pref_switches: List[str] = []
    while prefix_pred.get(entry) is not None:
        pv, sw = prefix_pred[entry]
        pref_switches.append(sw)
        pref_states.append(pv)
        entry = pv
    pref_states.reverse()
    pref_switches.reverse()
    return CanonicalLasso(pref_states, pref_switches,
                          cycle_states, cycle_switches,
                          candidate_entries=len(candidates))


# ------------------------------------------------------------------ 审计记录

def build_audit(
    spec: Dict[str, Any], original_total: Optional[int] = None
) -> Dict[str, Any]:
    """在冻结规格上求解规范最短违规执行审计，返回可 JSON 化的记录。

    ``spec`` 为 :func:`app.validation.validate_request` 归一化后的内部
    结构；``original_total`` 为来源复核任意套索的总切换数（有效上界）。
    公平集超过上限时抛 :class:`FairnessLimitExceeded`。
    """
    formula_ast = spec["formula_ast"]
    neg_nnf = push_negation(formula_ast, neg=True)
    gba = build_gba(neg_nnf)
    k = len(gba.events)
    if k > MAX_FAIRNESS_SETS:
        raise FairnessLimitExceeded(k)
    product = build_product(
        gba,
        spec["locations"],
        spec["initial"],
        spec["outgoing"],
        spec["propositions"],
    )
    lasso = find_canonical_lasso(product, original_total)

    n = len(product.states)
    fair_mask = [0] * n
    for g, group in enumerate(product.fairness):
        for v in group:
            fair_mask[v] |= 1 << g

    m = len(lasso.prefix_switches)
    r = len(lasso.cycle_switches)
    total = m + r
    q_states = lasso.prefix_states[:m] + lasso.cycle_states[:r]
    q_switches = lasso.prefix_switches + lasso.cycle_switches

    fairness_sets: List[Dict[str, Any]] = []
    for g, ev in enumerate(gba.events):
        witness = ev.a if ev.type == "eventually" else ev.b
        fairness_sets.append({
            "index": g,
            "eventuality": ev.to_str(),
            "kind": "eventually" if ev.type == "eventually" else "until",
            "hit_condition": (
                f"自动机状态见证 {witness.to_str()} 成立，"
                f"或未承诺事件性 {ev.to_str()}"
            ),
        })

    steps: List[Dict[str, Any]] = []
    for i, sid in enumerate(q_states):
        ps = product.states[sid]
        steps.append({
            "index": i,
            "phase": "prefix" if i < m else "loop",
            "location": ps.loc,
            "switch_taken": q_switches[i],
            "propositions": sorted(product.loc_labels[ps.loc]),
            "fairness_hits": [
                g for g in range(k) if (fair_mask[sid] >> g) & 1
            ],
        })
    coverage: Dict[str, List[int]] = {
        str(g): [i - m for i in range(m, total)
                 if (fair_mask[q_states[i]] >> g) & 1]
        for g in range(k)
    }

    # ---- 独立重放验证：起点、每条边真实存在、闭环非空且闭合、公平集全覆盖
    verification: List[str] = []

    def require(cond: bool, what: str) -> None:
        if not cond:
            raise AuditInvariantError(f"独立重放验证失败: {what}")
        verification.append(what)

    sw_decl = {sw["id"]: (sw["source"], sw["target"])
               for sw in spec["switches"]}
    require(q_states[0] in product.initial,
            "套索起点是否定自动机 × 规程的乘积初态")
    require(r >= 1, "闭环非空（至少一条切换）")
    for i in range(total):
        cur = q_states[i]
        nxt = q_states[i + 1] if i + 1 < total else q_states[m]
        sw = q_switches[i]
        require(sw in sw_decl, f"第 {i} 步切换 {sw} 已声明")
        src, dst = sw_decl[sw]
        require(product.states[cur].loc == src
                and product.states[nxt].loc == dst,
                f"第 {i} 步切换 {sw} 连接 {src} -> {dst} 真实存在")
        require(any(w == nxt and s == sw for w, s in product.edges[cur]),
                f"第 {i} 步乘积边 ({src} -> {dst}) 真实存在")
    require(lasso.cycle_states[0] == lasso.cycle_states[-1],
            "闭环闭合：末步回到闭环入口")
    for g in range(k):
        require(bool(coverage[str(g)]),
                f"闭环内命中公平集 {g}（{fairness_sets[g]['eventuality']}）")

    return {
        "kind": "canonical_shortest_violation_audit",
        "formula": spec["formula"],
        "initial": spec["initial"],
        "frozen_spec": {
            "locations": list(spec["locations"]),
            "initial": spec["initial"],
            "switches": [dict(sw) for sw in spec["switches"]],
            "propositions": {loc: list(ps)
                             for loc, ps in spec["propositions"].items()},
            "formula": spec["formula"],
        },
        "method": (
            "冻结来源规程/公式/初态，重新使用现有否定公式 GBA 与规程乘积；"
            "公平集命中展开为掩码层，在乘积图上精确求总切换数最小的可达"
            "接受套索（接受 SCC 限制 + 有效上界分支限界；非深度回放、"
            "非随机采样、不只在原位置图找环）"
        ),
        "fairness_set_count": k,
        "fairness_sets": fairness_sets,
        "canonical_lasso": {
            "kind": "lasso",
            "prefix_length": m,
            "cycle_length": r,
            "total_switches": total,
            "loop_start_index": m,
            "prefix_switches": list(lasso.prefix_switches),
            "cycle_switches": list(lasso.cycle_switches),
            "steps": steps,
            "loop_fairness_coverage": coverage,
            "tie_break": (
                "总切换数最小；同长度依次按前缀、闭环的切换标识序列"
                "字典序裁决，乘积状态签名兜底，结果唯一可复现"
            ),
            "verified": True,
            "verification": verification,
        },
        "comparison": {
            "original_total_switches": original_total,
            "canonical_total_switches": total,
            "saved_switches": (
                original_total - total
                if original_total is not None else None
            ),
        },
        "stats": {
            "fairness_sets": k,
            "product_states": n,
            "product_edges": sum(len(e) for e in product.edges),
            "candidate_loop_entries": lasso.candidate_entries,
        },
        "note": (
            "该套索在冻结的来源规程、公式与初态上精确求得：总切换数最小，"
            "同长度按前缀、闭环切换标识序列依次裁决；闭环非空、每条边真实"
            "存在且在闭环内命中每个公平集；重复发起审计得到同一套索。"
        ),
    }
