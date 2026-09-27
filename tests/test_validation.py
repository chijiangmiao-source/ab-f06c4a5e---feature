"""输入校验测试：非法公式 / 悬空端点 / 死端等必须定位拒绝。"""

import unittest

from app.validation import ValidationError, validate_request


def good(**over):
    payload = {
        "locations": ["a", "b"],
        "initial": "a",
        "switches": [
            {"id": "ab", "source": "a", "target": "b"},
            {"id": "ba", "source": "b", "target": "a"},
        ],
        "propositions": {"a": ["p"], "b": ["p"]},
        "formula": "G p",
    }
    payload.update(over)
    return payload


def errors_for(payload):
    try:
        validate_request(payload)
    except ValidationError as exc:
        return exc.errors
    return []


class TestStructureValidation(unittest.TestCase):
    def test_valid_request_passes(self):
        s = validate_request(good())
        self.assertEqual(s["locations"], ["a", "b"])
        self.assertIn("ab", [sw["id"] for sw in s["switches"]])

    def test_location_count_bounds(self):
        for n in (0, 1, 25):
            with self.subTest(n=n):
                locs = [f"s{i}" for i in range(n)]
                errs = errors_for(good(locations=locs, initial=None))
                self.assertTrue(any("位置数量" in e for e in errs))

    def test_duplicate_locations(self):
        errs = errors_for(good(locations=["a", "a"]))
        self.assertTrue(any("重复" in e for e in errs))

    def test_initial_must_exist(self):
        errs = errors_for(good(initial="zzz"))
        self.assertTrue(any("悬空初态" in e for e in errs))

    def test_dangling_switch_endpoint(self):
        bad = good(switches=[
            {"id": "ab", "source": "a", "target": "ghost"},
            {"id": "ba", "source": "b", "target": "a"},
        ])
        errs = errors_for(bad)
        self.assertTrue(any("悬空端点" in e and "ghost" in e for e in errs))

    def test_duplicate_switch_id(self):
        bad = good(switches=[
            {"id": "x", "source": "a", "target": "b"},
            {"id": "x", "source": "b", "target": "a"},
        ])
        errs = errors_for(bad)
        self.assertTrue(any("重复" in e for e in errs))

    def test_dead_end_rejected(self):
        # 位置 b 没有外出切换
        bad = good(switches=[{"id": "ab", "source": "a", "target": "b"}])
        errs = errors_for(bad)
        self.assertTrue(any("死端" in e and "'b'" in e for e in errs))

    def test_missing_proposition_block(self):
        bad = good(propositions={"a": ["p"]})
        errs = errors_for(bad)
        self.assertTrue(any("缺少位置 'b'" in e for e in errs))


class TestFormulaValidation(unittest.TestCase):
    def test_illegal_formulas(self):
        for f in ["p -> q", "F", "G  ", "(p", "p)", "p U q",
                  "p && q", "p + 1", "! ", "X", "p..q", ""]:
            with self.subTest(f=f):
                self.assertTrue(errors_for(good(formula=f)))

    def test_formula_only_allowed_chars(self):
        errs = errors_for(good(formula="G p; DROP TABLE"))
        self.assertTrue(any("不允许的字符" in e for e in errs))

    def test_undeclared_proposition_in_formula(self):
        errs = errors_for(good(formula="F granted"))
        self.assertTrue(any("未声明" in e and "granted" in e for e in errs))

    def test_valid_formulas_accepted(self):
        for f in ["G p", "F p", "X p", "!p", "p & p", "p | p",
                  "(p U p)", "G(!p | F p)"]:
            with self.subTest(f=f):
                self.assertEqual(errors_for(good(formula=f)), [])


if __name__ == "__main__":
    unittest.main()
