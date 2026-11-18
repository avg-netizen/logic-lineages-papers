# Independent exact pre-scope: InitialCode

Approved for proof development. All four frozen pins independently match.
Read actual definitions/targets, initialPeelingPass, rawNote encoding/decoding,
and current entries.tex initial-phase proof.

The code table uses the literal raw node coefficient-minus-one and tail fields,
expands multiplicities, and preserves descending order. OriginalUnitCodeCorrect
requires real ordinal CNF list equality and normality of every decoded exponent,
including the zero case; no list parser invariant is supplied as a premise.

The Boolean keeps equal leading charges, all remaining exponents below2, and
both exceptional shapes explicit. QuadraticRemainder requires first remaining
code2 and every further code1, excluding hidden higher-sensitive units. The
actual positive-limit semantic domain correctly excludes exponent-zero tails.
Both exceptional branches retain adjacent charges and min(c,d)+1+N(E) odd.
The proof must establish literal normal-code equality and N(omega^E)=1+N(E),
not merely substitute a semantic comparison oracle. E1/single-unit empty-tail
cases and zero coefficients represented through multiplicity remain covered.

All-input PR of both expanded unit list and joint initial predicate is required,
with exact normal-domain iff to existing initialPeelingPass. Strict tail-code
bounds, table lookup invariants, actual leading/log correspondence and CNF
reconstruction/uniqueness remain internal proof obligations.

Supporting executable initial front end only. Full equal-gap comparison still
needs combined tail sufficiency and original initial/pure-phase clock assembly.
No compiler or source/proof modification in this review.
