# Accepted supporting helper: congruence descends to divisors

The immutable target `InternalCongruenceDivisorTargets.ActualDivisor` is proved
by `InternalCongruenceDivisorProof.actualDivisor`. The exact alias
`InternalCongruenceDivisorStatementChecks.divisor_exact` has only
`propext`, `Classical.choice`, and `Quot.sound` in its actual axiom closure.

The proof eliminates the actual divisor existential to obtain m = r*d and the
actual two congruence witnesses to obtain a+q*m=b+p*m. It introduces q*r and p*r
as the new witnesses, using only internal equality congruence and multiplication
associativity. Arbitrary free names, contexts, terms and bodies remain literal.
This is a supporting CRT lemma, not bounded CRT or a numbered source completion.

Target-first passed: 1794004753910996564-5.json.
Initial proof failed only on an unopened rename namespace: failed-01.lean,
1794004782789223201-7.json. Second proof failed on an unopened product-renaming
namespace and ambiguous equationEmbedding name: failed-02.lean,
1794004796924224847-6.json. Both failed candidates and raw logs are retained.
The exact target was never edited. Final proof and alias passed:
1794004816001170793-7.json. Peak successful observed process-tree RSS was
1,198,884 KiB under the unchanged 1,536 MiB cap.

FROZEN.sha256 checks the pre-author target and suppliers; ACCEPTED.sha256 pins
all three new accepted source files. All frozen hashes rechecked successfully.
The serialized compiler slot was explicitly released to the parent after the
successful exact-alias check. No publication or commit was performed.
