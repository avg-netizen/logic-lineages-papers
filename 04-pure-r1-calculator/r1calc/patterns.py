"""Finite ordered respecting patterns and increasing map search.

These are finite syntax/graph predicates. They do not decide ordinal
realizability or recompute recursive Sigma1-elementarity inside a finite set.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations

from .ordinals import CNF, normal, resembles


class SearchLimitError(RuntimeError):
    """Incomplete finite enumeration; NEVER a nonexistence verdict."""


def _bound(limit):
    if limit is not None and (type(limit) is not int or limit < 0):
        raise ValueError("nonnegative candidate limit or None required")


@dataclass(frozen=True)
class Pattern:
    """Vertices 0..n-1 in fixed order, nested strict higher relations.

    Markers are optional syntax and ignored by maps unless preservation is
    explicitly requested. Order is implicit, not another supplied relation.
    """
    n: int
    relations: tuple[frozenset[tuple[int, int]], ...]
    marked: int | None = None

    def __post_init__(self):
        if (type(self.n) is not int or self.n < 0
                or type(self.relations) is not tuple or not self.relations):
            raise ValueError("nonnegative node count and nonempty relation tuple required")
        if self.marked is not None and (type(self.marked) is not int
                                       or not 0 <= self.marked < self.n):
            raise ValueError("integer marker must be inside the pattern")
        upper = frozenset(combinations(range(self.n), 2))
        for relation in self.relations:
            if type(relation) is not frozenset:
                raise ValueError("each relation must be a frozenset")
            for edge in relation:
                if (type(edge) is not tuple or len(edge) != 2
                        or any(type(x) is not int for x in edge)
                        or not 0 <= edge[0] < edge[1] < self.n):
                    raise ValueError("integer strict upper-triangular edge required")
            if not relation <= upper:
                raise ValueError("higher relation must be nested in preceding relation")
            for x, y, z in combinations(range(self.n), 3):
                if (x, y) in relation and (y, z) in relation and (x, z) not in relation:
                    raise ValueError("relation is not transitive")
                if ((x, y) in upper and (y, z) in upper and (x, z) in relation
                        and (x, y) not in relation):
                    raise ValueError("relation does not respect preceding relation")
            upper = relation

    @property
    def order(self) -> int:
        return len(self.relations)

    @property
    def node_count(self) -> int:
        return self.n

    @property
    def relation_bits(self) -> int:
        """Encoding capacity, not the number of true relation atoms."""
        return self.order * self.n * (self.n - 1) // 2


def _request(source, target, induced, preserve_marker):
    if not isinstance(source, Pattern) or not isinstance(target, Pattern):
        raise ValueError("source and target must be validated patterns")
    if type(induced) is not bool or type(preserve_marker) is not bool:
        raise ValueError("Boolean map flags required")
    if source.order != target.order:
        raise ValueError("signature/order mismatch")
    if preserve_marker and (source.marked is None or target.marked is None):
        raise ValueError("both markers required when preservation is requested")


def is_morphism(source: Pattern, target: Pattern, image: tuple[int, ...], *,
                induced: bool = False, preserve_marker: bool = False) -> bool:
    """Check one increasing image; malformed images raise ValueError."""
    _request(source, target, induced, preserve_marker)
    if (type(image) is not tuple or len(image) != source.n
            or any(type(i) is not int or not 0 <= i < target.n for i in image)
            or any(a >= b for a, b in zip(image, image[1:]))):
        raise ValueError("image must be an increasing tuple of target vertices")
    if preserve_marker and image[source.marked] != target.marked:
        return False
    for left, right in zip(source.relations, target.relations):
        for x, y in combinations(range(source.n), 2):
            held, mapped = (x, y) in left, (image[x], image[y]) in right
            if held and not mapped or induced and held != mapped:
                return False
    return True


def morphisms(source: Pattern, target: Pattern, *, induced=False,
              preserve_marker=False, max_candidates=None):
    """Stream all increasing maps, optionally bounding candidate images tried.

    A completed stream exhausts the finite binomial(target.n,source.n) images.
    If a supplied budget expires, SearchLimitError distinguishes incompleteness.
    """
    _request(source, target, induced, preserve_marker)
    _bound(max_candidates)
    for tried, image in enumerate(combinations(range(target.n), source.n)):
        if max_candidates is not None and tried >= max_candidates:
            raise SearchLimitError("candidate-image limit reached")
        if is_morphism(source, target, image, induced=induced,
                       preserve_marker=preserve_marker):
            yield image


def covers(source: Pattern, target: Pattern, **kwargs) -> bool:
    """Existence of a positive-preserving map (or flags explicitly supplied)."""
    return next(morphisms(source, target, **kwargs), None) is not None


def embeds(source: Pattern, target: Pattern, *, preserve_marker=False,
           max_candidates=None) -> bool:
    """Existence of an induced map, reflecting negative as well as positive atoms."""
    return covers(source, target, induced=True, preserve_marker=preserve_marker,
                  max_candidates=max_candidates)


def pure_r1_trace(ordinals: tuple[CNF, ...], marked=None) -> Pattern:
    """Inherit arithmetic R1 on increasing ambient coordinates; do not recompute it."""
    if (type(ordinals) is not tuple or any(not normal(a) for a in ordinals)
            or any(a >= b for a, b in zip(ordinals, ordinals[1:]))):
        raise ValueError("strictly increasing normal CNF coordinate tuple required")
    relation = frozenset((i, j) for i, j in combinations(range(len(ordinals)), 2)
                         if resembles(ordinals[i], ordinals[j]))
    return Pattern(len(ordinals), (relation,), marked)


def enumerate_patterns(n: int, order: int, *, max_candidates=None):
    """Stream finite syntaxes of given n/order, never semantic realizations.

    This exponential search tries subsets at every relation level. The optional
    budget counts ALL tested partial patterns; exhaustion raises, not returns
    an incomplete list as an exhaustive answer.
    """
    if type(n) is not int or type(order) is not int or n < 0 or order < 1:
        raise ValueError("nonnegative integer size and positive integer order required")
    _bound(max_candidates)
    pairs = tuple(combinations(range(n), 2))
    tried = 0

    def extend(relations, allowed):
        nonlocal tried
        for mask in range(1 << len(allowed)):
            if max_candidates is not None and tried >= max_candidates:
                raise SearchLimitError("partial-pattern candidate limit reached")
            tried += 1
            lower = frozenset(p for i, p in enumerate(allowed) if mask >> i & 1)
            try:
                candidate = Pattern(n, relations + (lower,))
            except ValueError:
                continue
            if len(candidate.relations) == order:
                yield candidate
            else:
                yield from extend(candidate.relations, tuple(sorted(lower)))

    yield from extend((), pairs)
