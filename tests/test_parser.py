"""解析器单测：合法语法、非法语法定位、F/G/U 展开。"""

import unittest

from app.ltl_parser import FormulaSyntaxError, parse_formula, subformulas


class TestParser(unittest.TestCase):
    def _ok(self, text, declared=None):
        return parse_formula(text, declared or {"p", "q", "request", "granted"})

    def test_basic_operators(self):
        for text in ["p", "!p", "p & q", "p | q", "X p", "F p", "G p",
                     "(p U q)", "G(!request | F granted)", "!!p",
                     "X X p", "G F p", "((p U q) U p)", "p&!q|Xp"]:
            with self.subTest(text=text):
                declared = {"p", "q", "request", "granted"}
                ast = parse_formula(text, declared)
                # 规范打印后再解析应得到同一棵 AST（幂等）
                again = parse_formula(ast.to_str(), declared)
                self.assertEqual(again, ast)

    def test_canonical_strings(self):
        d = {"p", "q"}
        self.assertEqual(parse_formula("F p", d).to_str(), "Fp")
        self.assertEqual(parse_formula("p & F q", d).to_str(), "(p & Fq)")
        self.assertEqual(parse_formula("G(!p | F q)", d).to_str(),
                         "G((!p | Fq))")
        self.assertEqual(parse_formula("(p U q)", d).to_str(), "(p U q)")

    def test_until_must_be_parenthesized(self):
        with self.assertRaises(FormulaSyntaxError) as cm:
            self._ok("p U q")
        self.assertIn("二元运算符", str(cm.exception))

    def test_illegal_chars_reported_with_position(self):
        for text in ["", "   ", "p -> q", "p ->", "p && q", "p + q",
                    "(p", "p)", "()", "!", "U", "X", "p &", "| p",
                    "F", "G ( )", "p q"]:
            with self.subTest(text=text):
                with self.assertRaises(FormulaSyntaxError):
                    self._ok(text)

    def test_error_position_is_1_based(self):
        try:
            self._ok("p &")
        except FormulaSyntaxError as exc:
            self.assertEqual(exc.pos, 2)  # 0-based 偏移 2 -> 字符 3
            self.assertIn("字符 3", str(exc))
        else:
            self.fail("应当抛出")

    def test_undeclared_proposition(self):
        with self.assertRaises(FormulaSyntaxError):
            parse_formula("F granted", {"request"})

    def test_subformulas_postorder(self):
        ast = self._ok("p & F q")
        subs = [s.to_str() for s in subformulas(ast)]
        self.assertLess(subs.index("p"), subs.index("(p & Fq)"))
        self.assertLess(subs.index("q"), subs.index("Fq"))
        self.assertLess(subs.index("Fq"), subs.index("(p & Fq)"))

    def test_whitespace_tolerated(self):
        self.assertEqual(self._ok("G  (  !p | F\tq )").to_str(),
                         "G((!p | Fq))")


if __name__ == "__main__":
    unittest.main()
