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
- **Paper 03, actual graph-image ideal core: checked.** Actual graph
  restrictions, hereditary directed images, language-cover transfer and their
  composed JEP criterion are proved. The original forbidden graph class still
  needs its checked identification with these parse images, so
  `lem:image-cover` remains pending.
  [Graph-image evidence](verification/repair-2026-10-31/RankedGraphImageStatementChecks.json)
  and [composition evidence](verification/repair-2026-10-31/RankedImageCoverCompletionStatementChecks.json).
- **Paper 03, executable pruning: checked.** Boolean leaf selection computes
  the literal deletion/suppression result, with exact empty-result and
  induced-image correctness.
  [Evidence](verification/repair-2026-10-31/RankedPruneAlgorithmStatementChecks.json).
- **Paper 05, actual source-policy separation: checked.** The closed typed
  source in the repair has positive ordinal coordinates 204 and 184 under
  the two specified policies. The left policy is calibrated against the
  existing literal partial operation. No collapse evaluation was used.
  [Evidence](verification/repair-2026-10-31/WWPolicyAssignmentStatementChecks.json).
- **Paper 05, generated assignment: checked suppliers.** Under either L/R
  policy, every original typed source has a syntax-directed assignment with
  the proved generated grades; positive coordinates are closed when free
  names are ground. This syntactic grading is not the original collapse-norm
  admissibility condition, and it is not a full scalar translation theorem.
  [Evidence](verification/repair-2026-10-31/WWPolicyGeneratedStatementChecks.json).
- **Paper 05, fixed-input partial values: checked.** For the same literal
  input tree, successful L partials have R partials with equal coordinate
  denotations for every valuation. This is compatible with the 204/184
  whole-source distinction, because policy-dependent assignments can supply
  different input trees to later partials. Arbitrary admissible policies and
  the remaining finite-expansion assertions are still pending.
  [Evidence](verification/repair-2026-10-31/WWPolicyValueStatementChecks.json).

After source reconciliation and this first whole-lemma acceptance, the register
contains **189 statements: 86 checked, 2 inherited calculator-package results,
and 101 pending**. The repair introduced eleven new numbered obligations.

## Work in progress

The next targets are the finite-forest-to-parse representation and actual
finite induced-subgraph-profile automaton for paper 03, and arbitrary binary
sum-shape expansion/value bounds for paper 05. Whole decision and norm claims remain pending until their full
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

The [second focused checkpoint](verification/repair-2026-10-31/checkpoint-02.json)
combines nine accepted gates and checks nineteen explicit exact-type aliases.
All 82 local closure source hashes match before and after compilation. The
root selects 714 gates; this remains a focused check, not a new whole-root
build. The register count remains 86 checked: the additional components are
explicit suppliers and implementations, not additional whole source results.
