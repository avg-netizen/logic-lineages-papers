import random
import unittest
from functools import lru_cache
from itertools import groupby

import r1calc as r


# Independent expanded hereditary words: every coefficient unit and exponent
# subtree is actually repeated. Only small inputs are sent to this reference.
def expand(a):
    return tuple(expand(e) for e, c in a for _ in range(c))


def compress(a):
    return tuple((compress(e), len(tuple(group))) for e, group in groupby(a))


def word_add(a, b):
    a = list(a)
    if b:
        while a and a[-1] < b[0]:
            a.pop()
    return tuple(a) + b


@lru_cache(None)
def word_endpoint(a):
    result = a
    if a:
        for exponent in a[-1]:
            result = word_add(result, word_endpoint((exponent,)))
    return result


def word_principal_sum(a):
    result = ()
    for exponent in a:
        result = word_add(result, word_endpoint((exponent,)))
    return result


def word_size(a):
    return sum(1 + word_size(e) for e in a)


def small_words(max_size=6):
    """Exhaust all normal expanded words up to a small tree norm."""
    levels = [{()}]
    for n in range(1, max_size + 1):
        candidates = sorted(set().union(*levels), reverse=True)
        current = set()

        def extend(prefix, start, remaining):
            if remaining == 0:
                current.add(prefix)
            for i in range(start, len(candidates)):
                e = candidates[i]
                cost = 1 + word_size(e)
                if cost <= remaining:
                    extend(prefix + (e,), i, remaining - cost)

        extend((), 0, n)
        levels.append(current)
    return sorted(set().union(*levels))


class ArithmeticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.words = small_words()

    def test_expanded_reference_all_small_terms(self):
        self.assertGreater(len(self.words), 50)
        for word in self.words:
            a = compress(word)
            self.assertTrue(r.normal(a))
            self.assertEqual(expand(r.endpoint(a)), word_endpoint(word))
            self.assertEqual(expand(r.principal_sum(a)), word_principal_sum(word))
            self.assertEqual(r.unary_tree_size(a), word_size(word))
            self.assertTrue(r.normal(r.endpoint(a)))
            self.assertEqual(r.endpoint(r.endpoint(a)), r.endpoint(a))
            n = word_size(word)
            self.assertLessEqual(r.unary_tree_size(r.endpoint(a)), n * (n + 1) // 2)

    def test_expanded_addition_order_and_right_products(self):
        for wa in self.words:
            a = compress(wa)
            for wb in self.words:
                b = compress(wb)
                self.assertEqual(expand(r.add(a, b)), word_add(wa, wb))
                self.assertEqual(r.compare(a, b), (wa > wb) - (wa < wb))
            for n in range(5):
                reference = ()
                for _ in range(n):
                    reference = word_add(reference, wa)
                self.assertEqual(expand(r.mul_nat(a, n)), reference)

    def test_examples_and_noncommutativity(self):
        w = r.OMEGA
        self.assertEqual(r.add(r.nat(2), w), w)
        self.assertNotEqual(r.add(w, r.nat(2)), w)
        self.assertEqual(r.endpoint(w), r.add(w, r.ONE))
        self.assertEqual(r.endpoint(r.power(r.nat(2))), r.add(r.power(r.nat(2)), r.nat(2)))
        self.assertEqual(r.endpoint(r.power(w)), r.parse_ordinal("w^w+w+1"))
        self.assertEqual(r.last_exponent(r.ZERO), r.ZERO)
        self.assertTrue(r.resembles(w, r.add(w, r.ONE)))
        self.assertFalse(r.resembles(w, r.add(w, r.nat(2))))
        self.assertFalse(r.resembles(r.ONE, r.ZERO))

    def test_tower_sharpness_instances(self):
        a = r.ZERO
        for n in range(11):
            self.assertEqual(r.unary_tree_size(a), n)
            self.assertEqual(r.unary_tree_size(r.endpoint(a)), n * (n + 1) // 2)
            a = r.power(a)

    def test_large_coefficients_stay_compressed(self):
        c = 10 ** 100
        a = r.power(r.OMEGA, c)
        self.assertEqual(len(a), 1)
        self.assertEqual(r.unary_tree_size(a), 3 * c)
        self.assertEqual(r.endpoint(a), r.add(a, r.parse_ordinal("w+1")))
        self.assertEqual(len(r.endpoint(a)), 3)
        self.assertEqual(r.mul_nat(a, 7)[0][1], 7 * c)

    def test_associativity_against_reference(self):
        rng = random.Random(151)
        for _ in range(100):
            a, b, c = (compress(rng.choice(self.words)) for _ in range(3))
            self.assertEqual(r.add(r.add(a, b), c), r.add(a, r.add(b, c)))

    def test_malformed_hereditary_inputs(self):
        bad = [None, [], 0, (1,), (((), 0),), (((), -1),), (((), True),),
               (([], 1),), (((), 1), ((), 2)), (((), 1), (r.ONE, 1)),
               (((((), 0),), 1),), (((), 1, 2),)]
        for a in bad:
            self.assertFalse(r.normal(a), repr(a))
            for call in (lambda: r.add(a, r.ZERO), lambda: r.add(r.ZERO, a),
                         lambda: r.mul_nat(a, 0), lambda: r.power(a),
                         lambda: r.endpoint(a), lambda: r.principal_sum(a),
                         lambda: r.pretty(a), lambda: r.unary_tree_size(a),
                         lambda: r.resembles(a, r.ZERO)):
                with self.assertRaises(ValueError):
                    call()
        for n in (-1, True, 1.0, "2"):
            with self.assertRaises(ValueError):
                r.nat(n)
            with self.assertRaises(ValueError):
                r.mul_nat(r.OMEGA, n)
        for n in (0, -1, True, "2"):
            with self.assertRaises(ValueError):
                r.power(r.ONE, n)


class ParserTests(unittest.TestCase):
    def test_roundtrip(self):
        for word in small_words():
            a = compress(word)
            self.assertEqual(r.parse_ordinal(r.pretty(a)), a)

    def test_precedence_and_expression_normalization(self):
        for text, expected in [("1+omega", "w"), ("ω+1", "w+1"),
                               ("(w+1)*2", "w*2+1"), ("w^0", "1"),
                               ("w*0", "0"), ("w+w", "w*2"),
                               ("w^w^2", "w^(w^2)"), ("w^(2*3)", "w^6")]:
            self.assertEqual(r.parse_ordinal(text), r.parse_ordinal(expected))

    def test_rejected_syntax_and_explicit_limits(self):
        for text in ("", "w+", "w**2", "2*w", "w*w", "-1", "w^(-1)",
                     "w^(1", "()", "w 2", "eps0", "__import__('os')", "w.foo", "w;1"):
            with self.assertRaises(ValueError, msg=text):
                r.parse_ordinal(text)
        with self.assertRaises(r.InputLimitError):
            r.parse_ordinal("w" * 5, max_chars=4)
        with self.assertRaises(r.InputLimitError):
            r.parse_ordinal("w^" * 8 + "1", max_depth=4)
        with self.assertRaises(r.InputLimitError):
            r.parse_ordinal("1" * 6, max_digits=5)


if __name__ == "__main__":
    unittest.main()
