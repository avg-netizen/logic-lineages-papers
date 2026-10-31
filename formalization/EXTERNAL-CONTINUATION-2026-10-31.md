# External continuation after the manuscript repairs

This round starts from commit `65d795b9c192a80c611010db63f120a9ce038388`,
which includes the previous accepted formalization checkpoint and the repairs
to papers 03 and 05. Work is on the cumulative branch
`formalization/external-continuation-2026-10-31`.

## Source changes

- Paper 03 replaces the problematic Carter transfer with an argument using
  ranked-tree ideals, graph images, and Parikh/Presburger inclusion. Its new
  binary parse relation is ordered dive/couple embedding. The old checked
  Carter counterexamples remain valid diagnostics of the earlier relations.
- Paper 05 fixes literal binary-expansion and padding conventions. Its
  translation is explicitly policy-relative. The corrected weak scalar and
  graded norm bounds do not assert convention-independent values or a full
  quantitative audit of the historical source.

The manuscript repair itself added no kernel-checked result. Historical
acceptance receipts and comparator hashes remain evidence for their original
statements, not automatic certificates of new or changed statements.

## Accepted components

- **Paper 03, `lem:parse-pruning`: checked in full.** The exact ranked
  dive/couple relation gives an induced embedding of evaluated graphs. Every
  nonempty leaf subset is exactly the image of a smaller parse. Both fixed
  statements passed, with only the ordinary allowed axioms.
  [Acceptance evidence](verification/repair-2026-10-31/RankedParseStatementChecks.json).
- **Paper 05, literal size bounds: checked suppliers.** The whole-free-first
  partial size is bounded by literal weighted size, itself bounded by
  `2^nodes - 1`; the corresponding finite-list multiplier bound also passed.
  This does **not** complete `wwsc:prop:finite`, whose assignment, output
  expansion and association-value assertions remain pending.
  [Acceptance evidence](verification/repair-2026-10-31/WWLiteralSizeStatementChecks.json).
- **Paper 03, finite ideal-cover criterion: checked supplier.** A finite
  hereditary directed cover has JEP exactly when one piece covers the class.
  The actual ranked-parse graph-image hypotheses are still separate work;
  this abstract result alone does not complete `lem:image-cover`.
  [Acceptance evidence](verification/repair-2026-10-31/FiniteIdealCoverStatementChecks.json).

After source reconciliation and this first whole-lemma acceptance, the register
contains **189 statements: 86 checked, 2 inherited calculator-package results,
and 101 pending**. The repair introduced eleven new numbered obligations.

## Work in progress

The first targets are actual ranked-parse induced embeddings and pruning for
paper 03, and literal partial-size bounds and explicit source-policy semantics
for paper 05. Whole decision and norm claims remain pending until their full
formal dependency chains are proved. In particular, bibliographic references
to effective ideal decomposition and Parikh's theorem are not Lean suppliers.

## Verification environment

This is a fresh checkout. The pinned Lean `v4.32.0-rc1` and Mathlib
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` have been restored using official
upstream caches. No upstream theorem rebuild was used. Local compilation uses
the existing serialized, bounded runner; exact gates and axiom audits are
required before acceptance. A comparator compile alone is not a proof.

CI diagnosis and repair remain deferred. No remote CI pass is claimed.
The new component sources and exact gates were directly compiled. Their
unchanged upstream dependencies used official cached objects. This round has
not yet rerun the entire historical root; the historical baseline evidence is
preserved separately. Raw receipt identities, actual axiom logs, source hashes
and the limits of the closure snapshots are recorded in the component evidence.

The first [focused checkpoint](verification/repair-2026-10-31/checkpoint-01.json)
combines these three gates and checks five explicit exact-type aliases. All
42 local source closure hashes match before and after compilation. The full
root now selects 708 gates, but only the focused aggregate was recompiled here.
An initial aggregate audit could not discover lazily imported declarations;
explicit aliases fixed audit visibility without changing any theorem or shared
build helper. Its failed receipt is preserved in the checkpoint record.
