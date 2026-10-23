"""Bounded command-line frontend; JSON errors never masquerade as negatives."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from . import (__version__, add, compare, endpoint, enumerate_patterns, lean_term,
               morphisms, mul_nat, parse_ordinal, pretty, principal_sum,
               pure_r1_trace, resembles, unary_tree_size)
from .jsonio import (MAX_BYTES, cnf_from_data, cnf_to_data, loads,
                     pattern_from_data, pattern_to_data)
from .parser import InputLimitError
from .patterns import SearchLimitError


def _read(path):
    if path == "-":
        data = sys.stdin.buffer.read(MAX_BYTES + 1)
    else:
        with Path(path).open("rb") as stream:
            data = stream.read(MAX_BYTES + 1)
    if len(data) > MAX_BYTES:
        raise InputLimitError("JSON file exceeds byte limit")
    return loads(data.decode("utf-8"))


def _ordinal(text):
    if text.startswith("@"):
        return cnf_from_data(_read(text[1:]))
    if text.startswith("json:"):
        return cnf_from_data(loads(text[5:]))
    return parse_ordinal(text)


def _description(a):
    return {"text": pretty(a), "cnf": cnf_to_data(a), "norm": unary_tree_size(a)}


def _emit(operation, fields):
    print(json.dumps({"schema": "r1calc.result.v1", "operation": operation, **fields},
                     sort_keys=True, ensure_ascii=False))


def _parser():
    p = argparse.ArgumentParser(prog="r1calc", description=__doc__)
    p.add_argument("--version", action="version", version=__version__)
    commands = p.add_subparsers(dest="operation", required=True)
    for name in ("endpoint", "principal-sum", "norm", "lean-term"):
        q = commands.add_parser(name)
        q.add_argument("ordinal")
        q.add_argument("--json", action="store_true")
    for name in ("add", "compare", "resembles"):
        q = commands.add_parser(name)
        q.add_argument("left")
        q.add_argument("right")
        q.add_argument("--json", action="store_true")
    q = commands.add_parser("mul-nat")
    q.add_argument("ordinal")
    q.add_argument("multiplier", type=int)
    q.add_argument("--json", action="store_true")
    q = commands.add_parser("trace")
    q.add_argument("ordinals", nargs="*")
    q.add_argument("--marked", type=int)
    q.add_argument("--json", action="store_true")
    q = commands.add_parser("validate-pattern")
    q.add_argument("pattern", help="JSON filename or - for stdin")
    q.add_argument("--json", action="store_true")
    q = commands.add_parser("maps")
    q.add_argument("source")
    q.add_argument("target")
    q.add_argument("--induced", action="store_true")
    q.add_argument("--preserve-marker", action="store_true")
    q.add_argument("--all", action="store_true", help="enumerate maps rather than find one")
    q.add_argument("--limit", type=int, default=20, help="output maps, maximum 1000")
    q.add_argument("--max-candidates", type=int, default=10000)
    q.add_argument("--json", action="store_true")
    q = commands.add_parser("patterns")
    q.add_argument("n", type=int)
    q.add_argument("--order", type=int, default=1)
    q.add_argument("--limit", type=int, default=20)
    q.add_argument("--max-candidates", type=int, default=10000)
    q.add_argument("--json", action="store_true")
    return p


def main(argv=None):
    args = _parser().parse_args(argv)
    op = args.operation
    try:
        if op in {"endpoint", "principal-sum", "norm", "lean-term", "mul-nat"}:
            a = _ordinal(args.ordinal)
            if op == "norm":
                result = unary_tree_size(a)
            elif op == "lean-term":
                result = lean_term(a)
            else:
                result = (endpoint(a) if op == "endpoint" else principal_sum(a)
                          if op == "principal-sum" else mul_nat(a, args.multiplier))
                if args.json:
                    fields = {"complete": True, "input": _description(a),
                              "result": _description(result)}
                    if op == "mul-nat":
                        fields["multiplier"] = args.multiplier
                    _emit(op, fields)
                else:
                    print(pretty(result))
                return 0
            if args.json:
                _emit(op, {"complete": True, "input": _description(a), "result": result})
            else:
                print(result)
        elif op in {"add", "compare", "resembles"}:
            a, b = _ordinal(args.left), _ordinal(args.right)
            if op == "add":
                result = add(a, b)
                if args.json:
                    _emit(op, {"complete": True, "left": _description(a),
                               "right": _description(b), "result": _description(result)})
                else:
                    print(pretty(result))
            else:
                result = compare(a, b) if op == "compare" else resembles(a, b)
                if args.json:
                    _emit(op, {"complete": True, "left": _description(a),
                               "right": _description(b), "result": result})
                else:
                    print(("<" if result < 0 else ">" if result > 0 else "=")
                          if op == "compare" else str(result).lower())
        elif op == "trace":
            coordinates = tuple(_ordinal(x) for x in args.ordinals)
            if len(coordinates) > 32:
                raise InputLimitError("CLI trace node limit is 32")
            trace = pure_r1_trace(coordinates, args.marked)
            _emit(op, {"complete": True, "coordinates": [cnf_to_data(x) for x in coordinates],
                       "pattern": pattern_to_data(trace), "inherited": True})
        elif op == "validate-pattern":
            pattern = pattern_from_data(_read(args.pattern))
            _emit(op, {"complete": True, "valid": True, "pattern": pattern_to_data(pattern)})
        elif op in {"maps", "patterns"}:
            if not 1 <= args.limit <= 1000 or not 0 <= args.max_candidates <= 1000000:
                raise ValueError("limit must be1..1000; candidate budget0..1000000")
            if op == "maps":
                if args.source == args.target == "-":
                    raise ValueError("source and target cannot both read stdin")
                source, target = pattern_from_data(_read(args.source)), pattern_from_data(_read(args.target))
                iterator = morphisms(source, target, induced=args.induced,
                                     preserve_marker=args.preserve_marker,
                                     max_candidates=args.max_candidates)
            else:
                if not 0 <= args.n <= 8 or not 1 <= args.order <= 8:
                    raise InputLimitError("CLI enumeration requires0<=n<=8,1<=order<=8")
                iterator = enumerate_patterns(args.n, args.order,
                                              max_candidates=args.max_candidates)
            results, complete, limited = [], True, None
            try:
                if op == "maps" and not args.all:
                    item = next(iterator, None)
                    if item is not None:
                        results.append(list(item))
                    _emit(op, {"complete": True, "exists": item is not None,
                               "images": results, "enumeration_complete": item is None,
                               "induced": args.induced, "preserve_marker": args.preserve_marker})
                    return 0
                for item in iterator:
                    if len(results) == args.limit:
                        complete, limited = False, "output limit reached"
                        break
                    results.append(list(item) if op == "maps" else pattern_to_data(item))
            except SearchLimitError as exc:
                complete, limited = False, str(exc)
            fields = {"complete": complete, "status": "complete" if complete else "limit",
                      "images" if op == "maps" else "patterns": results}
            if limited:
                fields["reason"] = limited
            if op == "maps":
                fields["exists"] = True if results else False if complete else None
                fields.update(induced=args.induced, preserve_marker=args.preserve_marker)
            else:
                fields.update(n=args.n, order=args.order)
            _emit(op, fields)
            return 0 if complete else 3
        return 0
    except (ValueError, OSError, UnicodeError, RecursionError) as exc:
        _emit(op, {"complete": False, "status": "input_error", "error": str(exc)})
        return 2
    except SearchLimitError as exc:
        _emit(op, {"complete": False, "status": "limit", "error": str(exc)})
        return 3


if __name__ == "__main__":
    raise SystemExit(main())
