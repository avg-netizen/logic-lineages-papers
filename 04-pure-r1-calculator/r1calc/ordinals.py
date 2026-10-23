"""Compressed hereditary Cantor normal forms below epsilon_0.

All additions and right multiplications by naturals are ORDINAL operations.
Coefficients stay compressed; ``unary_tree_size`` charges their expansion.
"""
from __future__ import annotations

from functools import lru_cache

CNF = tuple
ZERO: CNF = ()


def normal(a: object) -> bool:
    """Whether ``a`` is hereditary CNF with descending, positive blocks.

    Booleans are not natural coefficients. Shared exponent tuples are valid;
    their use as a compressed representation does not change the norm.
    """
    pending = [(a, False)]
    seen = set()
    while pending:
        node, ready = pending.pop()
        if type(node) is not tuple:
            return False
        if id(node) in seen:
            continue
        if not ready:
            for item in node:
                if (type(item) is not tuple or len(item) != 2
                        or type(item[1]) is not int or item[1] <= 0):
                    return False
            pending.append((node, True))
            pending.extend((e, False) for e, _ in node)
        else:
            if any(e >= previous for (previous, _), (e, _) in zip(node, node[1:])):
                return False
            seen.add(id(node))
    return True


def _require(a: CNF) -> None:
    if not normal(a):
        raise ValueError("normal hereditary CNF required")


def _natural(n: int) -> None:
    if type(n) is not int or n < 0:
        raise ValueError("natural number required (booleans excluded)")


def nat(n: int) -> CNF:
    _natural(n)
    return ((ZERO, n),) if n else ZERO


def power(exponent: CNF, coefficient: int = 1) -> CNF:
    """The normal block omega**exponent * coefficient; coefficient is positive."""
    _require(exponent)
    if type(coefficient) is not int or coefficient <= 0:
        raise ValueError("positive integer coefficient required")
    return ((exponent, coefficient),)


ONE = nat(1)
OMEGA = power(ONE)


def _add(a: CNF, b: CNF) -> CNF:
    if not b:
        return a
    lead, coefficient = b[0]
    keep = 0
    while keep < len(a) and a[keep][0] > lead:
        keep += 1
    if keep < len(a) and a[keep][0] == lead:
        return a[:keep] + ((lead, a[keep][1] + coefficient),) + b[1:]
    return a[:keep] + b


def add(a: CNF, b: CNF) -> CNF:
    """Ordinary ordinal addition a+b, which need not equal b+a."""
    _require(a)
    _require(b)
    return _add(a, b)


def _mul_nat(a: CNF, n: int) -> CNF:
    if not a or not n:
        return ZERO
    exponent, coefficient = a[0]
    return ((exponent, coefficient * n),) + a[1:]


def mul_nat(a: CNF, n: int) -> CNF:
    """Right ordinal multiplication a*n, without expanding n summands."""
    _require(a)
    _natural(n)
    return _mul_nat(a, n)


@lru_cache(maxsize=16384)
def _principal_sum(a: CNF) -> CNF:
    result = ZERO
    for exponent, coefficient in reversed(a):
        term = _add(((exponent, 1),), _principal_sum(exponent))
        result = _add(_mul_nat(term, coefficient), result)
    return result


def principal_sum(a: CNF) -> CNF:
    """P(0)=0; P(omega^e*c+t)=(omega^e+P(e))*c+P(t)."""
    _require(a)
    return _principal_sum(a)


def last_exponent(a: CNF) -> CNF:
    """Last CNF exponent; zero has last exponent zero by convention."""
    _require(a)
    return a[-1][0] if a else ZERO


def endpoint(a: CNF) -> CNF:
    """Arithmetic endpoint H(0)=0, H(a)=a+P(last_exponent(a)) for a>0."""
    _require(a)
    return _add(a, _principal_sum(a[-1][0])) if a else ZERO


def resembles(a: CNF, b: CNF) -> bool:
    """Arithmetic pure-R1 test a<=b<=H(a); semantic identification is external."""
    _require(a)
    _require(b)
    return a <= b <= endpoint(a)


def compare(a: CNF, b: CNF) -> int:
    _require(a)
    _require(b)
    return (a > b) - (a < b)


def unary_tree_size(a: CNF) -> int:
    """Expanded hereditary-CNF norm, charging EVERY coefficient repetition.

    W(0)=0; W(a)=sum c*(1+W(e)). This is not bit size, DAG size, runtime,
    a finite pattern's node count or its minimum ordinal realization size.
    """
    _require(a)

    def size(term):
        return sum(n * (1 + size(e)) for e, n in term)

    return size(a)


def pretty(a: CNF) -> str:
    """Readable expression accepted by parse_ordinal."""
    _require(a)

    def show(term):
        parts = []
        for e, n in term:
            if not e:
                parts.append(str(n))
            else:
                p = "w" if e == ONE else "w^(" + show(e) + ")"
                parts.append(p if n == 1 else p + "*" + str(n))
        return " + ".join(parts) if parts else "0"

    return show(a)


def lean_term(a: CNF) -> str:
    """ONote constructor syntax only; printing it does not prove a theorem."""
    _require(a)

    def show(term):
        if not term:
            return "ONote.zero"
        e, n = term[0]
        return f"(ONote.oadd {show(e)} {n} {show(term[1:])})"

    return show(a)
