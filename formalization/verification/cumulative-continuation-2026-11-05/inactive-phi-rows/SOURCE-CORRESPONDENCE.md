# Inactive plain-Phi name: finite cancellation branches

The original occurrence list is split by a finite Boolean mask. Admissible
masks delete only Phi occurrences and leave a row linear in the chosen name.
The actual cancellation guard proves the deleted subrow is zero, so the row
and either nonnegativity or divisibility atom retain their original meaning.

Coverage is required from literal inactive provenance: every actual equal-input
block touched by a Phi occurrence at the chosen name has coefficient zero.
Deleting the union of those whole blocks provides one enumerated admissible
mask. This includes zero coefficients, repeated names, shifted-input collisions
and cancellation with occurrences at other names. It does not assume an oracle
for exhaustive branches or change the definition of active provenance.

This is an atomic semantic reduction. It does not remove or move original domain
formulas and does not establish a numeric-code primitive-recursive program,
hyperPhi case, general source-case assembly or global nonlinear elimination.

## Corrected comparator and narrow acceptance

The first ActualInactiveAtom comparator omitted parentheses, so Lean parsed (inactive → output) ↔ input rather than inactive → (output ↔ input). That malformed freeze is explicitly abandoned; it is not proved or imported. The original freeze, reason and all six original source snapshots remain byte-preserved under abandoned-freezes/1793873281731958119-2. Only the corrected target, independently preflighted in receipt 1793873745364492992-2 and gated in 1793874023003771755-5, is accepted. Definitions and the other five targets are unchanged.

Acceptance is conditional atomic equivalence under the original plain-row and inactivity hypotheses. It does not justify contextual replacement underneath original domain formulas, nor numeric effectivity, HyperPhi or global elimination.
