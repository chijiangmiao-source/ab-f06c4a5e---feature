"""规范最短违规执行审计测试：精确最短、字典序裁决、公平集命中证据、
拒绝情形（成立/缺号/超限）与不改写来源复核。"""

import json
import tempfile
import threading
import unittest
import urllib.error
import urllib.request

from app.audit import (
    MAX_FAIRNESS_SETS,
    FairnessLimitExceeded,
    build_audit,
)
from app.checker import check
from app.server import create_server
from app.validation import validate_request


def spec_of(payload):
    return validate_request(payload)


def audit_of(payload):
    spec = spec_of(payload)
    result = check(spec)
    assert not result.holds, "测试模型必须判定不成立"
    v = result.violation
    original_total = v["prefix_length"] + v["cycle_length"]
    return build_audit(spec, original_total), original_total


def replay(payload, audit):
    """独立重放：每条边真实存在、闭环非空闭合、闭环命中每个公平集。"""
    cl = audit["canonical_lasso"]
    steps = cl["steps"]
    m = cl["loop_start_index"]
    total = len(steps)
    edge = {(sw["source"], sw["id"]): sw["target"] for sw in payload["switches"]}
    for i, st in enumerate(steps):
        dst = edge[(st["location"], st["switch_taken"])]
        nxt = steps[i + 1]["location"] if i + 1 < total else steps[m]["location"]
        assert dst == nxt, f"第 {i} 步切换不存在或不连通"
    assert cl["cycle_length"] >= 1, "闭环必须非空"
    for g in range(audit["fairness_set_count"]):
        assert any(
            i >= m for i, st in enumerate(steps) if g in st["fairness_hits"]
        ), f"公平集 {g} 必须在闭环内命中"


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
        "idle": [], "req": ["request"], "deny": ["denied"],
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


class TestCanonicalLasso(unittest.TestCase):
    def test_exact_minimum_simple(self):
        # 唯一违规闭环在 y 自环：最短 = 前缀 s2 + 闭环 s3
        audit, _ = audit_of({
            "locations": ["x", "y"], "initial": "x",
            "switches": [
                {"id": "s1", "source": "x", "target": "x"},
                {"id": "s2", "source": "x", "target": "y"},
                {"id": "s3", "source": "y", "target": "y"},
            ],
            "propositions": {"x": ["p"], "y": []},
            "formula": "G p",
        })
        cl = audit["canonical_lasso"]
        self.assertEqual(cl["total_switches"], 2)
        self.assertEqual(cl["prefix_switches"], ["s2"])
        self.assertEqual(cl["cycle_switches"], ["s3"])

    def test_strictly_shorter_than_original_lasso(self):
        # 初态 l0 上 p 即不成立：最短是 l0 自环 e0（总长 1），
        # 原任意套索走远路（总长 2）
        payload = {
            "locations": ["l0", "l1"], "initial": "l0",
            "switches": [
                {"id": "e0", "source": "l0", "target": "l0"},
                {"id": "e1", "source": "l0", "target": "l1"},
                {"id": "e2", "source": "l1", "target": "l1"},
                {"id": "e3", "source": "l1", "target": "l0"},
            ],
            "propositions": {"l0": ["q"], "l1": ["p", "q"]},
            "formula": "G p",
        }
        audit, original_total = audit_of(payload)
        cl = audit["canonical_lasso"]
        self.assertEqual(original_total, 2)
        self.assertEqual(cl["total_switches"], 1)
        self.assertEqual(cl["prefix_switches"], [])
        self.assertEqual(cl["cycle_switches"], ["e0"])
        self.assertEqual(audit["comparison"]["saved_switches"], 1)

    def test_loop_must_cover_multiple_fairness_sets(self):
        # k=2：单一位置无法同时命中两个公平集，最短闭环 y<->z（总长 3）
        payload = {
            "locations": ["x", "y", "z"], "initial": "x",
            "switches": [
                {"id": "t1", "source": "x", "target": "y"},
                {"id": "t2", "source": "y", "target": "z"},
                {"id": "t3", "source": "z", "target": "y"},
            ],
            "propositions": {"x": ["p", "q"], "y": ["q"], "z": ["p"]},
            "formula": "G p | G q",
        }
        audit, _ = audit_of(payload)
        cl = audit["canonical_lasso"]
        self.assertEqual(audit["fairness_set_count"], 2)
        self.assertEqual(cl["total_switches"], 3)
        self.assertEqual(cl["prefix_switches"], ["t1"])
        self.assertEqual(cl["cycle_switches"], ["t2", "t3"])
        cov = cl["loop_fairness_coverage"]
        self.assertTrue(cov["0"] and cov["1"])
        replay(payload, audit)

    def test_tie_break_by_switch_id_sequence(self):
        # 两条等长前缀切换 ta<tb、两条等长闭环切换 ty1<ty2：取字典序最小
        audit, _ = audit_of({
            "locations": ["x", "y"], "initial": "x",
            "switches": [
                {"id": "tb", "source": "x", "target": "y"},
                {"id": "ta", "source": "x", "target": "y"},
                {"id": "ty2", "source": "y", "target": "y"},
                {"id": "ty1", "source": "y", "target": "y"},
            ],
            "propositions": {"x": ["p"], "y": []},
            "formula": "G p",
        })
        cl = audit["canonical_lasso"]
        self.assertEqual(cl["total_switches"], 2)
        self.assertEqual(cl["prefix_switches"], ["ta"])
        self.assertEqual(cl["cycle_switches"], ["ty1"])

    def test_empty_prefix_when_initial_state_loops(self):
        # 闭环入口即初态：空前缀合法且字典序最小
        audit, _ = audit_of(STARVATION)
        cl = audit["canonical_lasso"]
        self.assertEqual(cl["total_switches"], 2)
        self.assertEqual(cl["prefix_switches"], [])
        self.assertEqual(cl["cycle_switches"], ["t1", "t2"])
        self.assertEqual(cl["loop_start_index"], 0)
        replay(STARVATION, audit)

    def test_zero_fairness_sets(self):
        # F p 的否定为 G!p：无公平集，任何非空闭环即可
        payload = {
            "locations": ["a", "b"], "initial": "a",
            "switches": [
                {"id": "aa", "source": "a", "target": "a"},
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "bb", "source": "b", "target": "b"},
            ],
            "propositions": {"a": [], "b": ["p"]},
            "formula": "F p",
        }
        audit, _ = audit_of(payload)
        cl = audit["canonical_lasso"]
        self.assertEqual(audit["fairness_set_count"], 0)
        self.assertEqual(cl["total_switches"], 1)
        self.assertEqual(cl["cycle_switches"], ["aa"])
        self.assertEqual(cl["loop_fairness_coverage"], {})
        replay(payload, audit)

    def test_fairness_limit_boundary(self):
        # k=6 可审计；k=7 明确拒绝
        for n_events, ok in ((MAX_FAIRNESS_SETS, True),
                             (MAX_FAIRNESS_SETS + 1, False)):
            props = [f"p{i}" for i in range(n_events)]
            formula = " | ".join(f"G {p}" for p in props)
            payload = {
                "locations": ["a", "b"], "initial": "a",
                "switches": [
                    {"id": "aa", "source": "a", "target": "a"},
                    {"id": "ab", "source": "a", "target": "b"},
                    {"id": "bb", "source": "b", "target": "b"},
                ],
                "propositions": {"a": [], "b": props},
                "formula": formula,
            }
            spec = spec_of(payload)
            result = check(spec)
            self.assertFalse(result.holds)
            self.assertEqual(result.stats["fairness_sets"], n_events)
            total = (result.violation["prefix_length"]
                     + result.violation["cycle_length"])
            if ok:
                audit = build_audit(spec, total)
                self.assertEqual(audit["fairness_set_count"], n_events)
                replay(payload, audit)
            else:
                with self.assertRaises(FairnessLimitExceeded):
                    build_audit(spec, total)

    def test_deterministic_reproducible(self):
        first, _ = audit_of(STARVATION)
        second, _ = audit_of(STARVATION)
        self.assertEqual(first["canonical_lasso"], second["canonical_lasso"])

    def test_steps_carry_fairness_hit_evidence(self):
        audit, _ = audit_of(STARVATION)
        cl = audit["canonical_lasso"]
        self.assertTrue(cl["verified"])
        for step in cl["steps"]:
            self.assertIn("location", step)
            self.assertIn("switch_taken", step)
            self.assertIsInstance(step["fairness_hits"], list)
            self.assertIn(step["phase"], ("prefix", "loop"))
        # 闭环内命中每个公平集的证据
        cov = cl["loop_fairness_coverage"]
        self.assertEqual(len(cov), audit["fairness_set_count"])
        for g, idxs in cov.items():
            self.assertTrue(idxs)
            for i in idxs:
                step = cl["steps"][cl["loop_start_index"] + i]
                self.assertIn(int(g), step["fairness_hits"])


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


class TestAuditHttpApi(AuditHttpTestBase):
    def _post_check(self, payload):
        status, body = self.request("POST", "/checks", payload)
        self.assertEqual(status, 201)
        return body

    def test_create_read_and_list_audit(self):
        created = self._post_check(STARVATION)
        chk_id = created["id"]
        original_total = (created["violation"]["prefix_length"]
                          + created["violation"]["cycle_length"])

        status, audit = self.request("POST", f"/checks/{chk_id}/audits")
        self.assertEqual(status, 201)
        self.assertEqual(audit["check_id"], chk_id)
        self.assertTrue(audit["id"].startswith("AUD-"))
        cl = audit["canonical_lasso"]
        # 规范最短：不长于来源的任意套索
        self.assertLessEqual(cl["total_switches"], original_total)
        self.assertGreaterEqual(cl["cycle_length"], 1)
        self.assertTrue(cl["verified"])
        for step in cl["steps"]:
            self.assertIn("location", step)
            self.assertIn("switch_taken", step)
            self.assertIn("fairness_hits", step)

        # 读取审计详情
        status, detail = self.request(
            "GET", f"/checks/{chk_id}/audits/{audit['id']}")
        self.assertEqual(status, 200)
        self.assertEqual(detail["id"], audit["id"])
        self.assertEqual(detail["canonical_lasso"], cl)

        # 列表
        status, listing = self.request("GET", f"/checks/{chk_id}/audits")
        self.assertEqual(status, 200)
        self.assertEqual([a["id"] for a in listing["audits"]], [audit["id"]])

    def test_audit_is_reproducible_and_source_untouched(self):
        created = self._post_check(STARVATION)
        chk_id = created["id"]
        status, before = self.request("GET", f"/checks/{chk_id}")
        self.assertEqual(status, 200)

        _, a1 = self.request("POST", f"/checks/{chk_id}/audits")
        _, a2 = self.request("POST", f"/checks/{chk_id}/audits")
        # 可稳定复现：同一规范最短套索；不同审计编号（审计轨迹追加）
        self.assertNotEqual(a1["id"], a2["id"])
        self.assertEqual(a1["canonical_lasso"], a2["canonical_lasso"])

        # 来源复核不被改写
        status, after = self.request("GET", f"/checks/{chk_id}")
        self.assertEqual(status, 200)
        self.assertEqual(before, after)

    def test_reject_when_source_holds(self):
        created = self._post_check(COMPLIANT)
        chk_id = created["id"]
        self.assertTrue(created["holds"])
        status, body = self.request("POST", f"/checks/{chk_id}/audits")
        self.assertEqual(status, 409)
        self.assertEqual(body["error"], "source_holds")
        # 不新增审计
        status, listing = self.request("GET", f"/checks/{chk_id}/audits")
        self.assertEqual(status, 200)
        self.assertEqual(listing["audits"], [])

    def test_reject_missing_check_id(self):
        status, body = self.request("POST", "/checks/CHK-999999/audits")
        self.assertEqual(status, 404)
        self.assertEqual(body["error"], "not_found")
        status, _ = self.request("GET", "/checks/CHK-999999/audits")
        self.assertEqual(status, 404)
        status, _ = self.request("GET", "/checks/CHK-999999/audits/AUD-000001")
        self.assertEqual(status, 404)

    def test_reject_fairness_limit(self):
        props = [f"p{i}" for i in range(MAX_FAIRNESS_SETS + 1)]
        payload = {
            "locations": ["a", "b"], "initial": "a",
            "switches": [
                {"id": "aa", "source": "a", "target": "a"},
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "bb", "source": "b", "target": "b"},
            ],
            "propositions": {"a": [], "b": props},
            "formula": " | ".join(f"G {p}" for p in props),
        }
        created = self._post_check(payload)
        self.assertFalse(created["holds"])
        chk_id = created["id"]
        status, body = self.request("POST", f"/checks/{chk_id}/audits")
        self.assertEqual(status, 422)
        self.assertEqual(body["error"], "fairness_limit_exceeded")
        # 不新增审计
        status, listing = self.request("GET", f"/checks/{chk_id}/audits")
        self.assertEqual(listing["audits"], [])

    def test_audit_uses_frozen_spec(self):
        created = self._post_check(STARVATION)
        chk_id = created["id"]
        status, audit = self.request("POST", f"/checks/{chk_id}/audits")
        self.assertEqual(status, 201)
        frozen = audit["frozen_spec"]
        self.assertEqual(frozen["locations"], STARVATION["locations"])
        self.assertEqual(frozen["initial"], STARVATION["initial"])
        self.assertEqual(frozen["formula"], STARVATION["formula"])
        self.assertEqual(frozen["switches"], STARVATION["switches"])

    def test_original_endpoints_still_work(self):
        # 原有 POST /checks 与 GET /checks/<id> 结论保持可用
        ok = self._post_check(COMPLIANT)
        self.assertTrue(ok["holds"])
        status, fetched = self.request("GET", f"/checks/{ok['id']}")
        self.assertEqual(status, 200)
        self.assertTrue(fetched["holds"])
        self.assertIn("negation_nnf", fetched["normalization"])

        bad = self._post_check(STARVATION)
        self.assertFalse(bad["holds"])
        status, fetched = self.request("GET", f"/checks/{bad['id']}")
        self.assertEqual(status, 200)
        self.assertFalse(fetched["holds"])
        self.assertIn("violation", fetched)


if __name__ == "__main__":
    unittest.main()
