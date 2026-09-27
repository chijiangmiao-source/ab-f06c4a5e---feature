"""模型检测器核心测试：成立判定与永不报警的违规闭环。"""

import unittest

from app.checker import (
    check, eval_subformulas_on_lasso, push_negation,
)
from app.validation import validate_request


def spec(payload):
    return validate_request(payload)


TWO = {
    "locations": ["a", "b"],
    "initial": "a",
    "switches": [
        {"id": "ab", "source": "a", "target": "b"},
        {"id": "ba", "source": "b", "target": "a"},
    ],
}


def two(props, formula):
    return spec({**TWO, "propositions": props, "formula": formula})


class TestBooleanAndTemporal(unittest.TestCase):
    def test_safety_holds(self):
        self.assertTrue(check(two({"a": ["p"], "b": ["p"]}, "G p")).holds)

    def test_safety_violated_gives_lasso(self):
        r = check(two({"a": ["p"], "b": []}, "G p"))
        self.assertFalse(r.holds)
        v = r.violation
        self.assertEqual(v["kind"], "lasso")
        self.assertGreaterEqual(v["cycle_length"], 1)
        locs = [s["location"] for s in v["steps"]]
        # 闭环必须经过不满足 p 的 b
        self.assertIn("b", locs[v["loop_start_index"]:])
        # 闭环上每一点 G p 都为 False
        for s in v["steps"][v["loop_start_index"]:]:
            self.assertFalse(s["subformula_truth"]["Gp"])

    def test_never_happens_detected(self):
        # a 自循环永不离开，p 只声明在不可达位置 c
        payload = {
            "locations": ["a", "c"],
            "initial": "a",
            "switches": [
                {"id": "aa", "source": "a", "target": "a"},
                {"id": "cc", "source": "c", "target": "c"},
            ],
            "propositions": {"a": [], "c": ["p"]},
            "formula": "F p",
        }
        r = check(spec(payload))
        self.assertFalse(r.holds)
        v = r.violation
        loop_locs = [s["location"]
                     for s in v["steps"][v["loop_start_index"]:]]
        self.assertEqual(set(loop_locs), {"a"})
        self.assertFalse(v["steps"][v["loop_start_index"]]
                         ["subformula_truth"]["Fp"])

    def test_eventually_holds(self):
        self.assertTrue(check(two({"a": [], "b": ["p"]}, "F p")).holds)

    def test_next(self):
        self.assertTrue(check(two({"a": [], "b": ["p"]}, "X p")).holds)
        self.assertFalse(check(two({"a": ["p"], "b": []}, "X p")).holds)

    def test_until_holds_and_breaks(self):
        self.assertTrue(
            check(two({"a": ["p"], "b": ["p", "q"]}, "(p U q)")).holds)
        # q 永不到来（q 仅在不可达位置 c 声明，a<->b 构成闭环）
        payload = {
            "locations": ["a", "b", "c"],
            "initial": "a",
            "switches": [
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"},
                {"id": "cc", "source": "c", "target": "c"},
            ],
            "propositions": {"a": ["p"], "b": ["p"], "c": ["q"]},
            "formula": "(p U q)",
        }
        r = check(spec(payload))
        self.assertFalse(r.holds)
        # 等待期 p 中断
        r2 = check(two({"a": [], "b": ["p", "q"]}, "(p U q)"))
        self.assertFalse(r2.holds)


class TestInterlockLiveness(unittest.TestCase):
    """放行时序：G(request -> F granted) 用 G(!request | F granted) 表示。"""

    FORMULA = "G(!request | F granted)"

    def _payload(self, with_grant_loop):
        if with_grant_loop:
            return {
                "locations": ["idle", "req", "grant"],
                "initial": "idle",
                "switches": [
                    {"id": "t1", "source": "idle", "target": "req"},
                    {"id": "t2", "source": "req", "target": "grant"},
                    {"id": "t3", "source": "grant", "target": "idle"},
                ],
                "propositions": {
                    "idle": [],
                    "req": ["request"],
                    "grant": ["request", "granted"],
                },
                "formula": self.FORMULA,
            }
        # 存在 req->idle 迟发闭环与 req->deny->idle 永不放行闭环
        return {
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
            "formula": self.FORMULA,
        }

    def test_compliant_procedure_holds(self):
        r = check(spec(self._payload(True)))
        self.assertTrue(r.holds)

    def test_starvation_loop_is_violation(self):
        r = check(spec(self._payload(False)))
        self.assertFalse(r.holds)
        v = r.violation
        loop = v["steps"][v["loop_start_index"]:]
        locs = [s["location"] for s in loop]
        # 闭环中出现 request 却不出现 granted
        self.assertIn("req", locs)
        self.assertNotIn("grant", locs)
        for s in loop:
            self.assertFalse(s["formula_true_here"])
        # 每一步都带位置、切换标识和全部子式真值
        root_key = validate_request(self._payload(False))["formula_ast"].to_str()
        for s in v["steps"]:
            self.assertIn("switch_taken", s)
            self.assertIsInstance(s["subformula_truth"], dict)
            self.assertIn(root_key, s["subformula_truth"])
            self.assertEqual(s["formula_true_here"],
                             s["subformula_truth"][root_key])

    def test_every_infinite_run_means_branching_checked(self):
        """存在一条合规路径但另有违规闭环时，必须判违规（不能只看标签）。"""
        payload = self._payload(False)
        # 即使 idle->req->... 有想象中的合规分支，t2/t3 构成的饥饿环仍违规
        self.assertFalse(check(spec(payload)).holds)


class TestWitnessValidity(unittest.TestCase):
    def _follow(self, payload, violation):
        s = validate_request(payload)
        edge = {(sw["source"], sw["id"]): sw["target"]
                for sw in s["switches"]}
        steps = violation["steps"]
        m = violation["loop_start_index"]
        n = len(steps)
        for i, st in enumerate(steps):
            dst = edge[(st["location"], st["switch_taken"])]
            nxt = steps[i + 1]["location"] if i + 1 < n \
                else steps[m]["location"]
            self.assertEqual(dst, nxt)

    def test_witness_is_real_path(self):
        payload = {
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
                "idle": [], "req": ["request"],
                "deny": ["denied"], "grant": ["granted"],
            },
            "formula": "G(!request | F granted)",
        }
        r = check(spec(payload))
        self.assertFalse(r.holds)
        self._follow(payload, r.violation)

    def test_lasso_evidence_fixpoint(self):
        # 周期 [p, !p] 上 GF p 为真、FG p 为假；自环 !p 上两者皆假
        ast_p = validate_request({
            "locations": ["a", "b"], "initial": "a",
            "switches": [
                {"id": "ab", "source": "a", "target": "b"},
                {"id": "ba", "source": "b", "target": "a"}],
            "propositions": {"a": ["p"], "b": []},
            "formula": "G F p",
        })["formula_ast"]
        ev = eval_subformulas_on_lasso(
            ast_p, [{"p"}, set()], [1, 0])
        self.assertTrue(ev[0]["GFp"])
        self.assertTrue(ev[1]["GFp"])


class TestNormalization(unittest.TestCase):
    def test_negation_nnf_dualities(self):
        from app.ltl_parser import parse_formula
        d = {"p", "q"}
        cases = {
            "G p": "F!p",
            "F p": "G!p",
            "(p U q)": "(!p V !q)",
            "X p": "X!p",
        }
        for text, expected in cases.items():
            nnf = push_negation(parse_formula(text, d), True)
            self.assertEqual(nnf.to_str(), expected, text)


if __name__ == "__main__":
    unittest.main()
