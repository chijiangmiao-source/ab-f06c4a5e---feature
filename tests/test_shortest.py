"""规范最短违规执行审计测试：

- 精确性：总切换数最小（不超过 checker 的任意套索），闭环非空、每条边
  真实存在、循环内命中每个公平集（独立重放校验）；
- 裁决：同长度依次按前缀、闭环的切换标识序列字典序；
- 证据：每步位置/切换/公平集命中，覆盖汇总在闭环下标内；
- 拒绝：来源成立 409、编号缺失 404、公平集超限 422，均不新增审计；
- 原有 POST /checks 与 GET /checks/<id> 结论不受影响，审计可复现。
"""

import json
import tempfile
import threading
import unittest
import urllib.error
import urllib.request

from app.checker import build_gba, build_product, check, push_negation
from app.server import create_server
from app.shortest import (
    MAX_FAIRNESS_SETS,
    FairnessLimitExceeded,
    find_shortest_lasso,
    replay_validate,
    run_shortest_audit,
)
from app.validation import validate_request


def spec(payload):
    return validate_request(payload)


def product_of(payload):
    s = spec(payload)
    neg_nnf = push_negation(s["formula_ast"], neg=True)
    gba = build_gba(neg_nnf)
    product = build_product(
        gba, s["locations"], s["initial"], s["outgoing"], s["propositions"]
    )
    return s, gba, product


STARVATION = {
    "locations": ["idle", "req", "deny", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "idle"},
        {"id": "t3", "source": "req", "target": "deny"},
        {"id": "t4", "source": "deny", "target": "idle"},
        {"id": "tg", "source": "grant", "target": "idle"},
    ],
    "propositions": {
        "idle": [],
        "req": ["request"],
        "deny": ["denied"],
        "grant": ["granted"],
    },
    "formula": "G(!request | F granted)",
}

COMPLIANT = {
    "locations": ["idle", "req", "grant"],
    "initial": "idle",
    "switches": [
        {"id": "t1", "source": "idle", "target": "req"},
        {"id": "t2", "source": "req", "target": "grant"},
        {"id": "t3", "source": "grant", "target": "idle"},
    ],
    "propositions": {"idle": [], "req": ["request"],
                     "grant": ["request", "granted"]},
    "formula": "G(!request | F granted)",
}

# 否定 NNF 为 F!a1 | ... | F!a7：7 个公平集，超过审计上限
SEVEN_FAIRNESS = {
    "locations": ["a", "b"],
    "initial": "a",
    "switches": [
        {"id": "ab", "source": "a", "target": "b"},
        {"id": "ba", "source": "b", "target": "a"},
    ],
    "propositions": {
        "a": [],
        "b": ["a1", "a2", "a3", "a4", "a5", "a6", "a7"],
    },
    "formula": "G a1 & G a2 & G a3 & G a4 & G a5 & G a6 & G a7",
}


class TestShortestLasso(unittest.TestCase):
    def test_starvation_minimal_beats_arbitrary(self):
        s, gba, product = product_of(STARVATION)
        lasso, _ = find_shortest_lasso(product)
        self.assertIsNotNone(lasso)
        # 精确最短：空前缀 + 闭环 idle -t1-> req -t2-> idle
        self.assertEqual(lasso.prefix_switches, [])
        self.assertEqual(lasso.cycle_switches, ["t1", "t2"])
        self.assertEqual(replay_validate(product, lasso), [])
        # 不劣于（严格短于或等于）checker 的任意套索
        arb = check(s).violation
        arb_total = arb["prefix_length"] + arb["cycle_length"]
        self.assertLessEqual(
            len(lasso.prefix_switches) + len(lasso.cycle_switches), arb_total
        )

    def test_prefix_tie_break_by_switch_id(self):
        # p1/p2 均为 s->w 的一步前缀，闭环为 w 自环；须选字典序最小的 p1
        payload = {
            "locations": ["s", "w", "z"],
            "initial": "s",
            "switches": [
                {"id": "p2", "source": "s", "target": "w"},
                {"id": "p1", "source": "s", "target": "w"},
                {"id": "c1", "source": "w", "target": "w"},
                {"id": "zz", "source": "z", "target": "z"},
            ],
            "propositions": {"s": [], "w": [], "z": ["p"]},
            "formula": "F p",
        }
        _, _, product = product_of(payload)
        lasso, _ = find_shortest_lasso(product)
        self.assertIsNotNone(lasso)
        self.assertEqual(lasso.prefix_switches, ["p1"])
        self.assertEqual(lasso.cycle_switches, ["c1"])
        self.assertEqual(replay_validate(product, lasso), [])

    def test_cycle_tie_break_by_switch_id(self):
        # 两条等长接受闭环 [a1,a2] 与 [b1,b2]；须选字典序最小的 a 环
        payload = {
            "locations": ["s", "x", "y", "z"],
            "initial": "s",
            "switches": [
                {"id": "b1", "source": "s", "target": "y"},
                {"id": "b2", "source": "y", "target": "s"},
                {"id": "a1", "source": "s", "target": "x"},
                {"id": "a2", "source": "x", "target": "s"},
                {"id": "zz", "source": "z", "target": "z"},
            ],
            "propositions": {
                "s": [],
                "x": ["request"],
                "y": ["request"],
                "z": ["granted"],
            },
            "formula": "G(!request | F granted)",
        }
        _, _, product = product_of(payload)
        lasso, _ = find_shortest_lasso(product)
        self.assertIsNotNone(lasso)
        self.assertEqual(lasso.prefix_switches, [])
        self.assertEqual(lasso.cycle_switches, ["a1", "a2"])
        self.assertEqual(replay_validate(product, lasso), [])

    def test_zero_fairness_sets_supported(self):
        # 纯安全式 G p：否定式无 F/U 事件性，公平集为 0，仍须精确求解
        payload = {
            "locations": ["a", "b"],
            "initial": "a",
            "switches": [
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
            ],
            "propositions": {"a": ["p"], "b": []},
            "formula": "G p",
        }
        _, _, product = product_of(payload)
        lasso, _ = find_shortest_lasso(product)
        self.assertIsNotNone(lasso)
        self.assertEqual(lasso.prefix_switches, [])
        self.assertEqual(lasso.cycle_switches, ["ab", "ba"])
        self.assertEqual(replay_validate(product, lasso), [])

    def test_deterministic_reproducible(self):
        _, _, product = product_of(STARVATION)
        first, _ = find_shortest_lasso(product)
        second, _ = find_shortest_lasso(product)
        self.assertEqual(first, second)

    def test_fairness_limit_raises(self):
        _, gba, product = product_of(SEVEN_FAIRNESS)
        self.assertGreater(len(gba.events), MAX_FAIRNESS_SETS)
        with self.assertRaises(FairnessLimitExceeded):
            find_shortest_lasso(product)

    def test_run_shortest_audit_evidence(self):
        s = spec(STARVATION)
        audit = run_shortest_audit(s, "CHK-000001")
        self.assertFalse(audit["holds"])
        self.assertEqual(audit["source_check_id"], "CHK-000001")
        self.assertEqual(audit["spec"]["formula"], STARVATION["formula"])
        v = audit["violation"]
        self.assertEqual(v["kind"], "minimal_lasso")
        self.assertEqual(
            v["total_switches"], v["prefix_length"] + v["cycle_length"]
        )
        self.assertGreaterEqual(v["cycle_length"], 1)
        m = v["loop_start_index"]
        steps = v["steps"]
        self.assertEqual(len(steps), v["total_switches"])
        # 每步位置/切换/公平集命中证据
        for st in steps:
            self.assertIn("location", st)
            self.assertIn("switch_taken", st)
            self.assertIsInstance(st["fairness_sets_hit"], list)
        # 每个公平集都在闭环下标范围内命中
        self.assertEqual(len(v["fairness_coverage"]),
                         audit["stats"]["fairness_sets"])
        for cov in v["fairness_coverage"]:
            self.assertTrue(cov["hit_step_indices"])
            self.assertTrue(all(m <= i < len(steps)
                                for i in cov["hit_step_indices"]))
        # 该公式下闭环逐点为假（无限违规，非有限回放）
        for st in steps[m:]:
            self.assertFalse(st["formula_true_here"])


class AuditHttpTestBase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.httpd = create_server("127.0.0.1", 0, self.tmp.name)
        self.port = self.httpd.server_address[1]
        self.thread = threading.Thread(target=self.httpd.serve_forever,
                                       daemon=True)
        self.thread.start()

    def tearDown(self):
        self.httpd.shutdown()
        self.httpd.server_close()
        self.thread.join(timeout=5)
        self.tmp.cleanup()

    def request(self, method, path, payload=None):
        data = None
        headers = {}
        if payload is not None:
            data = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json"
        req = urllib.request.Request(
            f"http://127.0.0.1:{self.port}{path}",
            data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=5) as resp:
                return resp.status, json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            return exc.code, json.loads(exc.read().decode("utf-8"))


class TestShortestAuditHttp(AuditHttpTestBase):
    def test_audit_success_and_source_untouched(self):
        status, created = self.request("POST", "/checks", STARVATION)
        self.assertEqual(status, 201)
        src_id = created["id"]
        src_total = (created["violation"]["prefix_length"]
                     + created["violation"]["cycle_length"])
        _, before = self.request("GET", f"/checks/{src_id}")

        status, audit = self.request(
            "POST", f"/checks/{src_id}/shortest-violation")
        self.assertEqual(status, 201)
        self.assertFalse(audit["holds"])
        self.assertEqual(audit["kind"], "shortest_violation_audit")
        self.assertEqual(audit["source_check_id"], src_id)
        v = audit["violation"]
        self.assertEqual(v["kind"], "minimal_lasso")
        self.assertEqual(v["total_switches"], 2)  # 空前缀 + [t1, t2]
        self.assertLessEqual(v["total_switches"], src_total)
        self.assertEqual(v["prefix_length"], 0)
        self.assertEqual([s["switch_taken"] for s in v["steps"]], ["t1", "t2"])
        for st in v["steps"]:
            self.assertIn("location", st)
            self.assertIsInstance(st["fairness_sets_hit"], list)
        self.assertTrue(all(c["hit_step_indices"]
                            for c in v["fairness_coverage"]))

        # 审计可按自身编号读取；来源复核不被改写
        status, fetched = self.request("GET", f"/checks/{audit['id']}")
        self.assertEqual(status, 200)
        self.assertEqual(fetched["id"], audit["id"])
        self.assertEqual(fetched["violation"]["kind"], "minimal_lasso")
        _, after = self.request("GET", f"/checks/{src_id}")
        self.assertEqual(before, after)
        self.assertEqual(after["violation"]["kind"], "lasso")

    def test_audit_is_reproducible(self):
        _, created = self.request("POST", "/checks", STARVATION)
        src_id = created["id"]
        _, a1 = self.request("POST", f"/checks/{src_id}/shortest-violation")
        _, a2 = self.request("POST", f"/checks/{src_id}/shortest-violation")
        self.assertNotEqual(a1["id"], a2["id"])
        self.assertEqual(a1["violation"], a2["violation"])

    def test_refusals_create_no_audit(self):
        # 来源成立 -> 409
        _, ok = self.request("POST", "/checks", COMPLIANT)
        self.assertTrue(ok["holds"])
        status, body = self.request(
            "POST", f"/checks/{ok['id']}/shortest-violation")
        self.assertEqual(status, 409)
        self.assertNotIn("id", body)

        # 编号缺失 -> 404
        status, body = self.request(
            "POST", "/checks/CHK-999999/shortest-violation")
        self.assertEqual(status, 404)
        self.assertNotIn("id", body)

        # 公平集超限 -> 422
        status, seven = self.request("POST", "/checks", SEVEN_FAIRNESS)
        self.assertEqual(status, 201)
        self.assertFalse(seven["holds"])
        self.assertEqual(seven["stats"]["fairness_sets"], 7)
        status, body = self.request(
            "POST", f"/checks/{seven['id']}/shortest-violation")
        self.assertEqual(status, 422)
        self.assertEqual(body["error"], "fairness_limit_exceeded")
        self.assertNotIn("id", body)

        # 以上拒绝均未占用审计编号：下一条成功复核应紧接上一编号
        status, nxt = self.request("POST", "/checks", COMPLIANT)
        self.assertEqual(status, 201)
        self.assertEqual(nxt["id"], "CHK-000003")

    def test_original_endpoints_unaffected(self):
        # 原有 POST /checks 与 GET /checks/<id> 结论保持可用
        status, body = self.request("POST", "/checks", COMPLIANT)
        self.assertEqual(status, 201)
        self.assertTrue(body["holds"])
        self.assertIn("negation_nnf", body["normalization"])
        status, fetched = self.request("GET", f"/checks/{body['id']}")
        self.assertEqual(status, 200)
        self.assertTrue(fetched["holds"])
        # 非法输入仍 400 且不生成审计
        bad = json.loads(json.dumps(COMPLIANT))
        bad["switches"][0]["target"] = "ghost"
        status, body = self.request("POST", "/checks", bad)
        self.assertEqual(status, 400)
        self.assertNotIn("id", body)


if __name__ == "__main__":
    unittest.main()
