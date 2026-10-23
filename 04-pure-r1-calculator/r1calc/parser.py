"""A small grammar for ordinal expressions; never evaluates Python code."""
from __future__ import annotations

from .ordinals import CNF, OMEGA, add, mul_nat, nat, power


class InputLimitError(ValueError):
    """An explicit input limit was reached, not an ordinal comparison result."""


def parse_ordinal(text: str, *, max_chars: int = 65536, max_depth: int = 64,
                  max_digits: int = 1000) -> CNF:
    """Parse naturals, w/omega/ω, +, parentheses, omega powers and *N.

    Addition and natural multiplication normalize ORDINAL expressions:
    ``1+w`` is w and ``(w+1)*2`` is w*2+1. General ordinal multiplication,
    subtraction, epsilon_0 and arbitrary identifiers are not in the grammar.
    """
    if type(text) is not str:
        raise ValueError("ordinal text must be a string")
    for limit in (max_chars, max_depth, max_digits):
        if type(limit) is not int or limit < 1:
            raise ValueError("positive parser limits required")
    if len(text) > max_chars:
        raise InputLimitError("ordinal text exceeds character limit")
    tokens = []
    i = 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c in "+*^()":
            tokens.append(c)
            i += 1
        elif "0" <= c <= "9":
            start = i
            while i < len(text) and "0" <= text[i] <= "9":
                i += 1
            if i - start > max_digits:
                raise InputLimitError("natural literal exceeds digit limit")
            tokens.append(int(text[start:i]))
        elif text.startswith("omega", i):
            tokens.append("w")
            i += 5
        elif c in "wω":
            tokens.append("w")
            i += 1
        else:
            raise ValueError(f"unexpected character at position {i}")
    if not tokens:
        raise ValueError("empty ordinal expression")
    cursor = 0

    def peek():
        return tokens[cursor] if cursor < len(tokens) else None

    def take(expected=None):
        nonlocal cursor
        value = peek()
        if value is None or expected is not None and value != expected:
            raise ValueError("incomplete ordinal expression or unmatched parentheses")
        cursor += 1
        return value

    def expression(depth):
        result = product(depth)
        while peek() == "+":
            take("+")
            result = add(result, product(depth))
        return result

    def atom(depth):
        if depth > max_depth:
            raise InputLimitError("ordinal nesting exceeds depth limit")
        token = take()
        if type(token) is int:
            return nat(token)
        if token == "(":
            value = expression(depth + 1)
            take(")")
            return value
        if token == "w":
            if peek() == "^":
                take("^")
                return power(atom(depth + 1))
            return OMEGA
        raise ValueError("expected natural, omega or parenthesized ordinal")

    def product(depth):
        result = atom(depth)
        if peek() == "*":
            take("*")
            n = take()
            if type(n) is not int:
                raise ValueError("only right multiplication by a natural is supported")
            result = mul_nat(result, n)
        return result

    result = expression(0)
    if cursor != len(tokens):
        raise ValueError("unexpected token; exponent sums must be parenthesized")
    return result
