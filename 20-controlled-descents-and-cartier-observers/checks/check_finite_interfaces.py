"""Finite checks of the new exact interfaces; not formal verification."""
from itertools import product
from math import factorial
from pathlib import Path
import json


def pmul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out


def pdivmod(a, b):
    q = 0
    while a and a.bit_length() >= b.bit_length():
        k = a.bit_length() - b.bit_length()
        q ^= 1 << k
        a ^= b << k
    return q, a


def pgcd(a, b):
    while b:
        a, b = b, pdivmod(a, b)[1]
    return a


def derivative(a):
    return sum(((a >> k) & 1) << (k - 1)
               for k in range(1, a.bit_length(), 2))


def select(a, bit):
    return sum(((a >> k) & 1) << ((k - bit) // 2)
               for k in range(bit, a.bit_length(), 2))


def denominator(d):
    a = 1
    for i in range(1, d + 1):
        a = pmul(a, (1 << i) | 1)
    return a


def step(u, a, bit):
    return select(pmul(u, a), bit)


def partition(d, n):
    values = [1] + [0] * n
    for i in range(1, d + 1):
        for j in range(i, n + 1):
            values[j] += values[j - i]
    return values[n]


# GF(16), using x^4+x+1. All odd orders through 5 divide 15.
def fmul(a, b):
    return pdivmod(pmul(a, b), 0b10011)[1]


def fpow(a, n):
    out = 1
    while n:
        if n & 1:
            out = fmul(out, a)
        a = fmul(a, a)
        n >>= 1
    return out


def finv(a):
    assert a
    return fpow(a, 14)


def peval(poly, z):
    out = 0
    for k in range(poly.bit_length() - 1, -1, -1):
        out = fmul(out, z) ^ ((poly >> k) & 1)
    return out


def squarefree_from_roots(roots):
    coeffs = [1]
    for z in roots:
        nxt = [0] * (len(coeffs) + 1)
        for k, value in enumerate(coeffs):
            nxt[k] ^= fmul(value, z)
            nxt[k + 1] ^= value
        coeffs = nxt
    assert all(value in (0, 1) for value in coeffs)
    return sum(value << k for k, value in enumerate(coeffs))


def poly_norm(a):
    return sum((i + 1) * coeff for i, coeff in enumerate(a))


def below_power(k, budget, length):
    out = [0] * length
    if not k or not budget:
        return out
    degree = min(k - 1, budget - 1)
    out[degree], remainder = divmod(budget, degree + 1)
    lower = below_power(degree, remainder, length)
    return [x + y for x, y in zip(out, lower)]


def max_below(a, budget):
    out = [0] * len(a)
    if not budget or not any(a):
        return out
    degree = max(i for i, value in enumerate(a) if value)
    multiplicity = a[degree]
    weight = degree + 1
    rest = list(a)
    rest[degree] = 0
    if any(rest) and multiplicity * weight <= budget:
        out[degree] = multiplicity
        lower = max_below(rest, budget - multiplicity * weight)
    else:
        out[degree] = min(
            multiplicity if any(rest) else multiplicity - 1,
            budget // weight,
        )
        lower = below_power(degree, budget - out[degree] * weight, len(a))
    return [x + y for x, y in zip(out, lower)]


def main():
    counts = {}
    checks = 0
    for d in range(1, 11):
        a = denominator(d)
        for n in range(129):
            u, rest = 1, n
            while rest:
                u = step(u, a, rest & 1)
                rest >>= 1
            assert (u & 1) == partition(d, n) % 2, (d, n)
            checks += 1
    counts["selected_coefficients"] = checks

    checks = 0
    for d in range(1, 7):
        a = denominator(d)
        roots = [z for z in range(1, 16) if peval(a, z) == 0]
        s = squarefree_from_roots(roots)
        ds = derivative(s)
        for u in range(1 << (s.bit_length() - 1)):
            residues = {z: fmul(peval(u, z), finv(peval(ds, z))) for z in roots}
            output = 0
            for z, residue in residues.items():
                assert residues[fmul(z, z)] == fmul(residue, residue)
                output ^= fmul(residue, finv(z))
            assert output == (u & 1)
            for bit in (0, 1):
                nxt = step(u, s, bit)
                for z, residue in residues.items():
                    actual = fmul(peval(nxt, z), finv(peval(ds, z)))
                    expected = fpow(residue if bit else fmul(z, residue), 8)
                    assert actual == expected, (d, u, bit, z)
                checks += 1
    counts["complete_profile_transitions"] = checks

    checks = 0
    for d in range(1, 5):
        a = denominator(d)
        degree = a.bit_length() - 1
        mu = sum(i & -i for i in range(1, d + 1))
        transient = (mu - 1).bit_length()
        for u in range(1 << degree):
            for word in product((0, 1), repeat=transient):
                nxt = u
                for bit in word:
                    nxt = step(nxt, a, bit)
                    assert nxt.bit_length() - 1 < degree
                reduced, rem = pdivmod(a, pgcd(nxt, a))
                assert not rem
                assert pgcd(reduced, derivative(reduced)) == 1
                checks += 1
    counts["arbitrary_word_pole_transients"] = checks

    checks, events = 0, 0
    for d in range(1, 4):
        for modulus in range(1, 4):
            period = factorial(d) * modulus ** (d - 1)
            for retained in range(3):
                for tail in range(3):
                    for residue in sorted({0, 1 % period, period - 1}):
                        representative = retained + residue
                        state = [tail] + [0] * (d - 1) + [1]
                        total = retained + poly_norm(state)
                        first = total + (representative - total) % period
                        count = 0
                        while any(state[1:]):
                            budget = first + min(count, 2) * period
                            assert budget >= retained + poly_norm(state)
                            state[0] = 0
                            state = max_below(state, budget - retained)
                            count += 1
                            assert count < 1000000
                        assert count % modulus == partition(d, residue) % modulus
                        checks += 1
                        events += count
    counts["congruent_growing_budget_segments"] = checks
    counts["budget_segment_events"] = events
    result = {"status": "PASS", "checks": counts,
              "scope": "Finite algebra and finite polynomial descents only; not a proof of the general theorems."}
    target = Path(__file__).with_name("FINITE-CHECK-RESULTS.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
