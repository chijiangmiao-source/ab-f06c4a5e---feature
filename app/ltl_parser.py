"""LTL 词法/语法解析与 AST 定义。

允许的公式语法（优先级从低到高）::

    expr := term ('|' term)*
    term := factor ('&' factor)*
    factor := '!' factor | 'X' factor | 'F' factor | 'G' factor | primary
    primary := 原子命题 | '(' expr ')'
    // 二元 U 只在括号内书写：``(a U b)``

允许字符仅限：声明的原子命题、``! & | X F G U`` 与括号、空白。
任何非法记号、空公式、括号错配、运算符缺操作数、未声明命题都会抛出
``FormulaSyntaxError``，消息带 1-based 字符位置，供接口精确定位拒绝。

注意：原子命题名不可以大写 ``F G X U`` 开头（``Fp`` 与算子应用 ``F p``
不可区分），也不允许使用保留名 ``true`` / ``false``。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Optional, Tuple


class FormulaSyntaxError(Exception):
    """公式语法非法；``pos`` 为 0-based 字符偏移（-1 表示整体/末尾）。"""

    def __init__(self, message: str, pos: int = -1):
        if pos >= 0:
            super().__init__(f"公式错误 @ 字符 {pos + 1}: {message}")
        else:
            super().__init__(message)
        self.pos = pos


_PRECEDENCE = {"and": 2, "or": 1, "until": 1}


@dataclass(frozen=True)
class Node:
    """不可变 AST 节点，可作集合/字典键。

    type ∈ atom / not / and / or / next / eventually / always / until /
    release（release 仅由否定归一化内部产生，用户语法不出现）。
    """

    type: str
    a: Optional["Node"] = None
    b: Optional["Node"] = None
    p: Optional[str] = None
    cs: Tuple["Node", ...] = field(default_factory=tuple)

    def to_str(self) -> str:
        t = self.type
        if t == "atom":
            return self.p
        if t == "not":
            return f"!{_wrap_unary(self.a)}"
        if t == "next":
            return f"X{_wrap_unary(self.a)}"
        if t == "eventually":
            return f"F{_wrap_unary(self.a)}"
        if t == "always":
            return f"G{_wrap_unary(self.a)}"
        sym = {"and": "&", "or": "|", "until": "U", "release": "V"}[t]
        return f"({self.a.to_str()} {sym} {self.b.to_str()})"

    def __str__(self) -> str:
        return self.to_str()


def _wrap_unary(n: Node) -> str:
    if n.type in ("and", "or", "until", "release"):
        return f"({n.to_str()})"
    return n.to_str()


class Parser:
    __slots__ = ("s", "n", "i", "declared")

    def __init__(self, text: str, declared: Optional[set] = None):
        self.s = text
        self.n = len(text)
        self.i = 0
        self.declared = declared

    def _skip_ws(self) -> None:
        while self.i < self.n and self.s[self.i] in " \t\r\n":
            self.i += 1

    def _peek(self) -> str:
        return self.s[self.i] if self.i < self.n else ""

    def parse(self) -> Node:
        self._skip_ws()
        if self.i >= self.n:
            raise FormulaSyntaxError("公式为空", -1)
        node = self._parse_or()
        self._skip_ws()
        if self.i < self.n:
            ch = self.s[self.i]
            if ch == "U":
                raise FormulaSyntaxError(
                    "'U' 是二元运算符，须写成 (左子式 U 右子式)", self.i
                )
            if ch == ")":
                raise FormulaSyntaxError("多余的右括号", self.i)
            if ch in "&|":
                raise FormulaSyntaxError(f"运算符 '{ch}' 缺少右操作数", self.i)
            raise FormulaSyntaxError(f"无法识别的字符 '{ch}'", self.i)
        return node

    def _parse_or(self) -> Node:
        left = self._parse_and()
        while True:
            self._skip_ws()
            if self._peek() == "|":
                pos = self.i
                self.i += 1
                self._skip_ws()
                if self._at_operand_end():
                    raise FormulaSyntaxError("'|' 缺少右操作数", pos)
                left = Node("or", left, self._parse_and())
            else:
                return left

    def _parse_and(self) -> Node:
        left = self._parse_unary()
        while True:
            self._skip_ws()
            if self._peek() == "&":
                pos = self.i
                self.i += 1
                self._skip_ws()
                if self._at_operand_end():
                    raise FormulaSyntaxError("'&' 缺少右操作数", pos)
                left = Node("and", left, self._parse_unary())
            else:
                return left

    def _at_operand_end(self) -> bool:
        return self.i >= self.n or self.s[self.i] in ")&|"

    def _parse_unary(self) -> Node:
        self._skip_ws()
        ch = self._peek()
        if ch in "!XFG":
            pos = self.i
            self.i += 1
            self._skip_ws()
            if self._at_operand_end():
                raise FormulaSyntaxError(f"'{ch}' 缺少操作数", pos)
            sub = self._parse_unary()
            if ch == "!":
                return Node("not", sub)
            if ch == "X":
                return Node("next", sub)
            if ch == "F":
                return Node("eventually", sub)
            return Node("always", sub)
        if ch == "V":
            raise FormulaSyntaxError(
                "'V'(release) 不在允许的运算符内", self.i
            )
        if ch == "U":
            raise FormulaSyntaxError(
                "'U' 是二元运算符，须写成 (左子式 U 右子式)", self.i
            )
        return self._parse_primary()

    def _parse_primary(self) -> Node:
        self._skip_ws()
        if self.i >= self.n:
            raise FormulaSyntaxError("此处缺少操作数", self.i)
        ch = self.s[self.i]
        if ch == "(":
            return self._parse_paren()
        if ch in ")&|":
            raise FormulaSyntaxError(f"意外的字符 '{ch}'", self.i)
        if ch[0].isalpha() or ch == "_":
            return self._parse_atom()
        raise FormulaSyntaxError(f"无法识别的字符 '{ch}'", self.i)

    def _parse_paren(self) -> Node:
        open_pos = self.i
        self.i += 1  # (
        self._skip_ws()
        if self._peek() == ")":
            raise FormulaSyntaxError("括号内为空", open_pos)
        node = self._parse_or()
        self._skip_ws()
        # 括号内允许一个顶层二元 U
        if self._peek() == "U":
            self.i += 1
            self._skip_ws()
            if self._at_operand_end():
                raise FormulaSyntaxError("'U' 缺少右操作数", open_pos)
            right = self._parse_or()
            node = Node("until", node, right)
            self._skip_ws()
        if self.i >= self.n or self.s[self.i] != ")":
            raise FormulaSyntaxError("缺少右括号", open_pos)
        self.i += 1
        return node

    def _parse_atom(self) -> Node:
        start = self.i
        if self.s[self.i] == "_":
            # 允许下划线标识符
            while self.i < self.n and (
                self.s[self.i].isalnum() or self.s[self.i] == "_"
            ):
                self.i += 1
        else:
            while self.i < self.n and (
                self.s[self.i].isalnum() or self.s[self.i] == "_"
            ):
                self.i += 1
        word = self.s[start:self.i]
        if self.declared is not None and word not in self.declared:
            raise FormulaSyntaxError(
                f"未声明的原子命题 '{word}'", start
            )
        return Node("atom", p=word)


def parse_formula(text: str, declared: Optional[set] = None) -> Node:
    """解析公式；``declared`` 给定时校验原子命题必须已声明。"""
    if not isinstance(text, str):
        raise FormulaSyntaxError("公式必须是字符串", -1)
    return Parser(text, declared).parse()


# --------------------------------------------------------------------- 遍历

def walk(node: Node):
    """后序遍历（含多目 cs 节点；自动机内部使用）。"""
    t = node.type
    if t == "atom":
        yield node
        return
    if t in ("not", "next", "eventually", "always"):
        yield from walk(node.a)
        yield node
        return
    if t == "cs":
        for c in node.cs:
            yield from walk(c)
        yield node
        return
    yield from walk(node.a)
    yield from walk(node.b)
    yield node


def subformulas(root: Node) -> List[Node]:
    """结构去重的全部子式，后序排列（子式先于父式）。"""
    out: List[Node] = []
    seen = set()
    for n in walk(root):
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out
