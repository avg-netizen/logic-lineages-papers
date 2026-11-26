#!/usr/bin/env python3
"""Bounded literal-AST control for GENERATED-WITNESS.md; never evaluates psi.

Only the Var/Lam/App original-source fragment needed by the named witness is
implemented. This is not an alternative ordinal evaluator or a general source
soundness test. A single worker takes the existing resource mutex, uses at most
512 MiB address space and 60 CPU/wall seconds, and requires 1536 MiB headroom.
"""

from __future__ import annotations

from dataclasses import dataclass
import fcntl
import hashlib
import json
from pathlib import Path
import resource
import signal
import sys
import time


@dataclass(frozen=True)
class O:
    tag: str
    args: tuple[O, ...] = ()
    name: str = ""
    index: int = -1


ONE = O("one")


def add(f: O, g: O) -> O:
    return O("add", (f, g))


def psi(f: O, g: O) -> O:
    return O("psi", (f, g))


def xfree(h: O, name: str) -> bool:
    return not (h.tag == "var" and h.name == name) and all(
        xfree(a, name) for a in h.args
    )


def subones(h: O, name: str) -> O:
    if h.tag == "var" and h.name == name:
        return ONE
    return O(h.tag, tuple(subones(a, name) for a in h.args), h.name, h.index)


def sx(h: O, name: str) -> int:
    if xfree(h, name) or h.tag == "var":
        return 1
    f, g = h.args
    return (2 if h.tag == "exp" else 1) * sx(f, name) + sx(g, name) + 1


def nodes(h: O) -> int:
    return 1 + sum(nodes(a) for a in h.args)


def finite(h: O) -> int:
    """Exact finite value; refuse psi rather than approximating its control."""
    if h.tag == "one":
        return 1
    if h.tag == "add":
        return sum(finite(a) for a in h.args)
    if h.tag == "exp":
        return 2 ** finite(h.args[0]) * finite(h.args[1])
    raise ValueError(f"not an elementary closed finite coordinate: {h.tag}")


@dataclass(frozen=True)
class Policy:
    active_sum: str

    def summation(self, site: str, operands: list[O]) -> O:
        assert operands
        # Box convention fixed as f0+(g0+n); repeats fixed left in both.
        right = site == "box-tail" or (
            site == "active-sum" and self.active_sum == "right"
        )
        if right:
            h = operands[-1]
            for f in reversed(operands[:-1]):
                h = add(f, h)
            return h
        h = operands[0]
        for f in operands[1:]:
            h = add(h, f)
        return h

    def repeat(self, count: int, h: O) -> O:
        assert count > 0
        return self.summation("repeat", [h] * count)


@dataclass(frozen=True)
class Vec:
    cells: tuple[O, ...]

    @property
    def level(self) -> int:
        return len(self.cells) - 1


def partial(p: Policy, name: str, k: int, i: int, h: O) -> Vec:
    n = k + 1
    if xfree(h, name):
        return Vec(tuple(add(h, ONE) if i == j else ONE for j in range(n + 1)))
    if h.tag == "var":
        assert h.name == name and h.index == i
        return Vec((ONE,) * (n + 1))
    f, g = h.args
    if h.tag == "add":
        a, b = partial(p, name, k, i, f), partial(p, name, k, i, g)
        return Vec(tuple(p.summation("active-sum", [a.cells[j], b.cells[j], ONE])
                         for j in range(n + 1)))
    if h.tag == "exp":
        assert i > 0
        a, b = partial(p, name, k, i + 1, f), partial(p, name, k, i, g)
        return Vec(tuple(p.summation("active-exp", [p.repeat(2, a.cells[j]),
                                                     b.cells[j], ONE])
                         for j in range(n + 1)))
    assert h.tag == "psi" and i == 0
    a, b = partial(p, name, k, 1, f), partial(p, name, k, 0, g)
    return Vec((psi(subones(f, name), b.cells[0]),) + tuple(
        add(a.cells[j], b.cells[j]) for j in range(1, n + 1)))


def abstract(p: Policy, name: str, k: int, h: Vec) -> tuple[Vec, dict]:
    n, m = k + 1, h.level
    parts = [partial(p, name, k, i, a) for i, a in enumerate(h.cells)]
    sizes = [sx(a, name) for a in h.cells]
    factor = 2 ** n * sum(sizes)
    delta = [p.repeat(factor, parts[0].cells[0])]
    for j in range(1, max(n, m) + 1):
        delta.append(p.summation("delta-positive", [a.cells[j] for a in parts])
                     if j <= n else h.cells[j])
    result = []
    for j, a in enumerate(delta):
        # Only a missing coordinate is elided; no value-based zero rewrite.
        result.append(add(a, subones(h.cells[j], name)) if j <= m else a)
    return Vec(tuple(result)), {"input_sizes": sizes, "factor": factor,
                               "positive_partial_values":
                               [[finite(a.cells[j]) for j in range(1, n + 1)]
                                for a in parts]}


@dataclass(frozen=True)
class Ty:
    args: tuple[Ty, ...] = ()

    @property
    def level(self) -> int:
        return 0 if not self.args else max(self.args[0].level + 1, self.args[1].level)


GROUND = Ty()


@dataclass(frozen=True)
class Term:
    tag: str
    ty: Ty
    args: tuple[Term, ...] = ()
    name: str = ""
    binder_ty: Ty | None = None


def var(name: str, ty: Ty = GROUND) -> Term:
    return Term("var", ty, name=name)


def lam(name: str, body: Term, ty: Ty = GROUND) -> Term:
    return Term("lam", Ty((ty, body.ty)), (body,), name, ty)


def app(f: Term, g: Term) -> Term:
    assert f.ty.args and f.ty.args[0] == g.ty
    return Term("app", f.ty.args[1], (f, g))


def box(p: Policy, f: Vec, g: Vec) -> Vec:
    assert f.level > g.level
    n = g.level
    h = list(f.cells)
    for i in range(n, 0, -1):
        h[i] = O("exp", (h[i + 1], add(f.cells[i], g.cells[i])))
    operands = [f.cells[0], g.cells[0]]
    if n > 0:
        operands.append(p.repeat(n, ONE))
    h[0] = psi(h[1], p.summation("box-tail", operands))
    return Vec(tuple(h))


def assignment(p: Policy, t: Term, trace: dict) -> Vec:
    if t.tag == "var":
        return Vec(tuple(O("var", name=t.name, index=i) for i in range(t.ty.level + 1)))
    if t.tag == "lam":
        assert t.binder_ty is not None
        result, stats = abstract(p, t.name, t.binder_ty.level,
                                 assignment(p, t.args[0], trace))
        assert result.level == t.ty.level
        trace[t.name] = stats
        return result
    assert t.tag == "app"
    f, g = (assignment(p, a, trace) for a in t.args)
    return Vec(box(p, f, g).cells[:t.ty.level + 1])


def digest(h: O) -> str:
    d = hashlib.sha256()
    def visit(a: O) -> None:
        d.update(json.dumps([a.tag, a.name, a.index], separators=(",", ":")).encode())
        for b in a.args:
            visit(b)
    visit(h)
    return d.hexdigest()


def run() -> dict:
    source = lam("z", lam("x", app(lam("w", var("z")), var("x"))))
    result = {}
    for association, expected in (("left", 204), ("right", 184)):
        trace: dict = {}
        a = assignment(Policy(association), source, trace)
        actual = finite(a.cells[1])
        assert actual == expected
        assert trace["x"]["factor"] == 10
        assert trace["z"]["input_sizes"] == ([193, 1] if association == "left" else [173, 1])
        assert trace["z"]["factor"] == (388 if association == "left" else 348)
        assert all(xfree(c, name) for c in a.cells for name in ("w", "x", "z"))
        result[association] = {"positive_coordinate": actual, "trace": trace,
                               "actual_level": a.level,
                               "node_counts": [nodes(c) for c in a.cells],
                               "literal_tree_sha256": [digest(c) for c in a.cells]}
    return {"source": "lambda z:o. lambda x:o. ((lambda w:o. z) x)",
            "source_level": source.ty.level, "policies": result,
            "psi_evaluations": 0, "claim": "named witness only"}


if __name__ == "__main__":
    mem = next(int(a.split()[1]) for a in Path("/proc/meminfo").read_text().splitlines()
               if a.startswith("MemAvailable:"))
    if mem < 1536 * 1024:
        raise SystemExit("RESOURCE_REFUSAL: less than 1536 MiB MemAvailable")
    with open("/tmp/logic-lineages-ii5-reverse-compute.lock", "a") as mutex:
        try:
            fcntl.flock(mutex, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit("RESOURCE_REFUSAL: shared compute mutex busy")
        resource.setrlimit(resource.RLIMIT_AS, (512 * 1024 * 1024,) * 2)
        resource.setrlimit(resource.RLIMIT_CPU, (60, 60))
        signal.alarm(60)
        started = time.monotonic()
        report = run()
        report["elapsed_seconds"] = time.monotonic() - started
        report["peak_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        report["memavailable_start_kib"] = mem
        report["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        print(json.dumps(report, indent=2))
