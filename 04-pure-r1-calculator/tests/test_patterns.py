import itertools
import unittest

import r1calc as r


def reference_valid(n, relations):
    """Full reflexive matrices/all triples, independently of strict-triple code."""
    previous = {(i, j) for i in range(n) for j in range(n) if i <= j}
    for edges in relations:
        current = set(edges) | {(i, i) for i in range(n)}
        if not current <= previous:
            return False
        for x, y, z in itertools.product(range(n), repeat=3):
            if (x, y) in current and (y, z) in current and (x, z) not in current:
                return False
            if ((x, y) in previous and (y, z) in previous
                    and (x, z) in current and (x, y) not in current):
                return False
        previous = current
    return True


def reference_patterns(n, order):
    pairs = list(itertools.combinations(range(n), 2))
    for colors in itertools.product(range(order + 1), repeat=len(pairs)):
        relations = tuple(frozenset(p for p, color in zip(pairs, colors) if color > j)
                          for j in range(order))
        if reference_valid(n, relations):
            yield relations


def reference_maps(source, target, induced=False, marked=False):
    """Enumerate ALL functions; derive increasing injections by direct tests."""
    result = set()
    for image in itertools.product(range(target.n), repeat=source.n):
        if any(image[i] >= image[j] for i in range(source.n) for j in range(i + 1, source.n)):
            continue
        if marked and image[source.marked] != target.marked:
            continue
        valid = True
        for level in range(source.order):
            for i, j in itertools.product(range(source.n), repeat=2):
                old = (i, j) in source.relations[level]
                new = (image[i], image[j]) in target.relations[level]
                if old and not new or induced and old != new:
                    valid = False
        if valid:
            result.add(image)
    return result


class PatternTests(unittest.TestCase):
    def test_exhaustive_small_validation_and_enumeration(self):
        counts = []
        for n in range(5):
            row = []
            for order in (1, 2):
                expected = set(reference_patterns(n, order))
                actual = {p.relations for p in r.enumerate_patterns(n, order)}
                self.assertEqual(actual, expected)
                row.append(len(actual))
            counts.append(row)
        self.assertEqual(counts, [[1, 1], [1, 1], [2, 3], [5, 14], [14, 84]])
        self.assertEqual({p.relations for p in r.enumerate_patterns(3, 3)},
                         set(reference_patterns(3, 3)))

    def test_every_small_map_against_all_functions(self):
        patterns = [p for n in range(4) for p in r.enumerate_patterns(n, 2)]
        for source in patterns:
            for target in patterns:
                for induced in (False, True):
                    expected = reference_maps(source, target, induced)
                    actual = set(r.morphisms(source, target, induced=induced))
                    self.assertEqual(actual, expected)
                    self.assertEqual(r.covers(source, target, induced=induced), bool(expected))

    def test_covering_induced_and_marker_distinctions(self):
        discrete = r.Pattern(2, (frozenset(),))
        chain = r.Pattern(2, (frozenset({(0, 1)}),))
        self.assertTrue(r.covers(discrete, chain))
        self.assertFalse(r.embeds(discrete, chain))
        self.assertFalse(r.covers(chain, discrete))
        self.assertTrue(r.embeds(chain, chain))
        left = r.Pattern(2, (frozenset(),), 0)
        right = r.Pattern(2, (frozenset(),), 1)
        self.assertTrue(r.covers(left, right))
        self.assertFalse(r.covers(left, right, preserve_marker=True))
        singleton = r.Pattern(1, (frozenset(),), 0)
        self.assertEqual(set(r.morphisms(singleton, right, preserve_marker=True)), {(1,)})
        self.assertEqual(set(r.morphisms(singleton, right, preserve_marker=True)),
                         reference_maps(singleton, right, marked=True))
        empty = r.Pattern(0, (frozenset(),))
        self.assertEqual(list(r.morphisms(empty, chain)), [()])
        self.assertTrue(r.covers(empty, chain))

    def test_composition(self):
        source = r.Pattern(1, (frozenset(),), 0)
        middle = r.Pattern(2, (frozenset(),), 1)
        target = r.Pattern(3, (frozenset(),), 2)
        for f in r.morphisms(source, middle, induced=True, preserve_marker=True):
            for g in r.morphisms(middle, target, induced=True, preserve_marker=True):
                self.assertTrue(r.is_morphism(source, target, tuple(g[i] for i in f),
                                             induced=True, preserve_marker=True))

    def test_inherited_trace_and_validation(self):
        a, b = r.OMEGA, r.add(r.OMEGA, r.ONE)
        trace = r.pure_r1_trace((a, b), marked=1)
        self.assertEqual(trace.relations, (frozenset({(0, 1)}),))
        self.assertEqual(trace.relation_bits, 1)
        self.assertTrue(r.embeds(trace, trace, preserve_marker=True))
        for coords in ((a, a), (b, a), [a, b], ([],)):
            with self.assertRaises(ValueError):
                r.pure_r1_trace(coords)

    def test_invalid_patterns_requests_and_images(self):
        invalid = [(True, (frozenset(),), None), (2, [], None),
                   (2, (frozenset(),), True), (0, (frozenset(),), 0),
                   (2, (frozenset({(False, 1)}),), None),
                   (2, (frozenset({(0, 0)}),), None),
                   (2, (frozenset({(-1, 1)}),), None),
                   (3, (frozenset({(0, 2)}),), None),
                   (3, (frozenset({(0, 1), (1, 2)}),), None),
                   (2, (frozenset(), frozenset({(0, 1)})), None)]
        for n, relations, marker in invalid:
            with self.assertRaises(ValueError):
                r.Pattern(n, relations, marker)
        a = r.Pattern(1, (frozenset(),))
        b = r.Pattern(1, (frozenset(), frozenset()))
        for call in (lambda: r.covers(a, b), lambda: r.covers(a, a, preserve_marker=True),
                     lambda: r.covers(a, a, induced=1)):
            with self.assertRaises(ValueError):
                call()
        for image in ([], (True,), (-1,), (1,), (), (0, 0)):
            with self.assertRaises(ValueError):
                r.is_morphism(a, a, image)

    def test_explicit_limits_never_mean_nonexistence(self):
        a = r.Pattern(1, (frozenset(),))
        with self.assertRaises(r.SearchLimitError):
            r.covers(a, a, max_candidates=0)
        with self.assertRaises(r.SearchLimitError):
            list(r.enumerate_patterns(3, 2, max_candidates=1))
        for args in ((True, 1), (2, True), (-1, 1), (1, 0)):
            with self.assertRaises(ValueError):
                list(r.enumerate_patterns(*args))


if __name__ == "__main__":
    unittest.main()
