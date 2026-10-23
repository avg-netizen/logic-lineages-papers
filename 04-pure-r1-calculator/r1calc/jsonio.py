"""Strict, bounded JSON interchange using only ordinary JSON data."""
from __future__ import annotations

import json

from .ordinals import CNF, normal
from .parser import InputLimitError
from .patterns import Pattern

MAX_BYTES = 1 << 20


def loads(text: str):
    """JSON without duplicate object keys, nonfinite values or enormous literals."""
    if type(text) is not str or len(text.encode("utf-8")) > MAX_BYTES:
        raise InputLimitError("JSON input exceeds byte limit")

    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate JSON object key")
            result[key] = value
        return result

    def integer(value):
        if len(value.lstrip("-")) > 1000:
            raise InputLimitError("JSON integer exceeds digit limit")
        return int(value)

    def nonfinite(_):
        raise ValueError("nonfinite JSON number is not supported")

    try:
        return json.loads(text, object_pairs_hook=object_pairs, parse_int=integer,
                          parse_constant=nonfinite)
    except RecursionError as exc:
        raise InputLimitError("JSON nesting exceeds decoder capacity") from exc


def cnf_to_data(a: CNF):
    if not normal(a):
        raise ValueError("normal hereditary CNF required")

    def encode(term):
        return [[encode(e), c] for e, c in term]

    return encode(a)


def cnf_from_data(data, *, max_depth=64, max_blocks=10000) -> CNF:
    """Decode raw nested CNF arrays, or a versioned ordinal wrapper.

    JSON CNFs are checked, not silently reordered, merged or normalized.
    max_blocks counts block occurrences across the entire input tree.
    """
    if any(type(x) is not int or x < 1 for x in (max_depth, max_blocks)):
        raise ValueError("positive JSON limits required")
    if type(data) is dict:
        if set(data) != {"schema", "cnf"} or data["schema"] != "r1calc.ordinal.v1":
            raise ValueError("unknown ordinal JSON schema or fields")
        data = data["cnf"]
    count = 0

    def decode(node, depth):
        nonlocal count
        if depth > max_depth:
            raise InputLimitError("CNF exceeds JSON depth limit")
        if type(node) is not list:
            raise ValueError("CNF node must be an array")
        result = []
        for item in node:
            count += 1
            if count > max_blocks:
                raise InputLimitError("CNF exceeds JSON block limit")
            if (type(item) is not list or len(item) != 2
                    or type(item[1]) is not int or item[1] <= 0):
                raise ValueError("CNF block must be [exponent,positive integer]")
            result.append((decode(item[0], depth + 1), item[1]))
        term = tuple(result)
        if not normal(term):
            raise ValueError("CNF exponents must be strictly descending and normal")
        return term

    return decode(data, 0)


def pattern_to_data(pattern: Pattern):
    if not isinstance(pattern, Pattern):
        raise ValueError("validated Pattern required")
    return {"schema": "r1calc.pattern.v1", "n": pattern.n,
            "relations": [[list(e) for e in sorted(r)] for r in pattern.relations],
            "marked": pattern.marked}


def pattern_from_data(data, *, max_nodes=32, max_order=8) -> Pattern:
    """Decode a finite pattern; duplicates and malformed atoms are rejected."""
    if any(type(x) is not int or x < 1 for x in (max_nodes, max_order)):
        raise ValueError("positive pattern decoder limits required")
    if type(data) is not dict:
        raise ValueError("pattern must be a JSON object")
    fields = set(data)
    if "schema" in fields:
        if data["schema"] != "r1calc.pattern.v1":
            raise ValueError("unknown pattern JSON schema")
        fields.remove("schema")
    if fields != {"n", "relations", "marked"}:
        raise ValueError("pattern fields must be n,relations,marked")
    n, relations = data["n"], data["relations"]
    if type(n) is not int or n < 0:
        raise ValueError("nonnegative integer node count required")
    if n > max_nodes:
        raise InputLimitError("pattern exceeds node limit")
    if type(relations) is not list or not relations:
        raise ValueError("nonempty relation array required")
    if len(relations) > max_order:
        raise InputLimitError("pattern exceeds signature-order limit")
    out = []
    for edges in relations:
        if type(edges) is not list:
            raise ValueError("relation must be an edge array")
        pairs = []
        for edge in edges:
            if (type(edge) is not list or len(edge) != 2
                    or any(type(v) is not int for v in edge)):
                raise ValueError("edge must contain two integers")
            pairs.append(tuple(edge))
        if len(set(pairs)) != len(pairs):
            raise ValueError("duplicate relation edge")
        out.append(frozenset(pairs))
    return Pattern(n, tuple(out), data["marked"])
