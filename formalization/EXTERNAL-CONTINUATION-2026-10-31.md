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
  These inequalities alone do not complete `wwsc:prop:finite`; the later
  combined finite-expansion result below supplies the remaining assertions.
  [Acceptance evidence](verification/repair-2026-10-31/WWLiteralSizeStatementChecks.json).
- **Paper 03, finite ideal-cover criterion: checked supplier.** A finite
  hereditary directed cover has JEP exactly when one piece covers the class.
  This abstract result alone does not complete `lem:image-cover`; the actual
  graph-image hypotheses are discharged by the later results below.
  [Acceptance evidence](verification/repair-2026-10-31/FiniteIdealCoverStatementChecks.json).
- **Paper 03, actual graph-image ideal core: checked.** Actual graph
  restrictions, hereditary directed images, language-cover transfer and their
  composed JEP criterion are proved. These initial core components alone did
  not identify the original forbidden class with the image; the later
  representation results below discharge that gap.
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
  different input trees to later partials. Arbitrary-policy and composed
  expansion coverage is recorded separately below.
  [Evidence](verification/repair-2026-10-31/WWPolicyValueStatementChecks.json).
- **Paper 03, `lem:image-cover`: checked in full.** Every finite order forest
  has an actual ranked-parse graph representation. This identifies the
  permitted graph class with its parse-language image, first for the original
  forest input and then for every finite forbidden graph family with P4/C4
  adjoined. In the source's nonempty branch, the theorem derives actual class
  coverage, hereditary/JEP pieces and the equality criterion from the given
  finite term-ideal cover. No representation theorem is left as a premise.
  [Representation evidence](verification/repair-2026-10-31/ForestParseRepresentationStatementChecks.json)
  and [general-family evidence](verification/repair-2026-10-31/ForestParseRepresentationGeneralStatementChecks.json).
- **Paper 03, finite profile automaton: checked suppliers.** The executable
  fixed-size Boolean graph-code transition and run exactly track induced
  embeddings, acceptance and downward closure. The later uniform encoding and
  source-language adapter below complete the full regularity lemma.
  [Evidence](verification/repair-2026-10-31/FiniteProfileStatementChecks.json).
- **Paper 05, arbitrary structural associations: checked suppliers.** Ordered
  full binary sums use every operand unchanged and once, have the exact
  added-node count, and preserve the fixed-list ordinal value. The actual
  partial recursion under any structural site/arity policy preserves generated
  grades and has policy-independent values on the same input. These are not
  claims that an arbitrary policy function is computable, nor original norm
  admissibility results.
  [Sum-shape evidence](verification/repair-2026-10-31/WWAdmissibleSumStatementChecks.json)
  and [partial evidence](verification/repair-2026-10-31/WWAdmissiblePartialStatementChecks.json).
- **Paper 03, `lem:parse-regular`: checked in full.** A finite-matrix input
  algorithm constructs an actual finite ranked machine for arbitrary finite
  forbidden graph families, with P4/C4 adjoined. Common-size encoding,
  padding, empty forbidden graphs, semantic recognition and literal ranked
  downward closure are all covered. Classical representation completeness
  for abstract finite graphs is not used as a computational oracle.
  [Encoding evidence](verification/repair-2026-10-31/ProfileAutomatonEncodingStatementChecks.json)
  and [source-language evidence](verification/repair-2026-10-31/ProfileSourceRegularStatementChecks.json).
- **Paper 03, canonical-cotree ingredients: checked suppliers.** Actual
  graph isomorphisms respect association, swaps and congruence; root and
  complement connectivity distinguish union/join. Connected-fiber recovery
  also gives actual component permutations and fiber isomorphisms. Full
  reduced-cotree construction, uniqueness and binary characterization remain
  pending.
  [AC evidence](verification/repair-2026-10-31/ForestParseRepresentationACStatementChecks.json)
  and [component evidence](verification/repair-2026-10-31/ForestParseRepresentationComponentsStatementChecks.json).
- **Paper 05, arbitrary-policy assignments and local expansion bounds:
  checked suppliers.** All original typed sources have generated assignments
  under every structural macro policy, with ground-context positive
  closedness. Partial outputs satisfy `6*3^inputNodes`, positive repeats have
  the exact node count, and positive box outputs satisfy the source recurrence.
  The later combined theorem adds the whole-source bound and full intended
  partial-domain coverage to these local formulas.
  [Assignment evidence](verification/repair-2026-10-31/WWAdmissibleAssignmentStatementChecks.json)
  and [expansion evidence](verification/repair-2026-10-31/WWAdmissibleExpansionStatementChecks.json).
- **Paper 05, `wwsc:prop:finite`: checked in full.** An independently defined
  literal syntactic domain includes whole-free promotion and all actual
  partial recursion clauses. Partials and all original zero-history source
  assignments have unique finite outputs, with proved executable numerical
  bounds independent of policy. Partial values for the same literal input
  are invariant under all structural policies. This stronger scope includes
  computable policies without claiming that arbitrary selectors themselves
  are computable. It does not claim original norm admissibility or scalar
  translation/evaluation.
  [Composed-bound evidence](verification/repair-2026-10-31/WWAdmissibleAssignmentBoundStatementChecks.json)
  and [whole-proposition evidence](verification/repair-2026-10-31/WWLiteralPartialDomainStatementChecks.json).
- **Paper 03, exact exceptional decisions: checked suppliers.** Symbolic
  finite-state saturation decides emptiness of the actual source machine.
  An empty forbidden graph or empty parse language gives a proved sound
  partial YES answer for actual graph-class JEP; other cases return no answer.
  [Emptiness evidence](verification/repair-2026-10-31/ProfileLanguageEmptyStatementChecks.json)
  and [exception evidence](verification/repair-2026-10-31/ProfileExceptionalDecisionStatementChecks.json).
- **Paper 03, reduced cotree uniqueness: checked supplier.** Actual reduced
  multiway cotrees have the required component semantics, and graph
  isomorphism recovers their recursive unordered structure with multiplicity.
  Whole canonical-cotree coverage still needs the complete existence and
  binary-expansion chain.
  [Evidence](verification/repair-2026-10-31/ForestParseRepresentationCotreeStatementChecks.json).
- **Paper 05, finite-tail collapse facts: checked suppliers.** Actual
  finite-tail norm/increment monotonicity and natural finite-right sum
  calibration support the weak scalar proof. These are not global collapse
  monotonicity and do not replace the original bounded-substitution domain.
  [Tail evidence](verification/repair-2026-10-31/WWFiniteTailMonotonicityStatementChecks.json)
  and [calibration evidence](verification/repair-2026-10-31/WWFiniteNaturalTailStatementChecks.json).

After source reconciliation and four whole-statement acceptances, the register
contains **189 statements: 89 checked, 2 inherited calculator-package results,
and 98 pending**. The repair introduced eleven new numbered obligations.

## Work in progress

The next targets are complete canonical cotree/binary expansion and actual
CFG transition semantics for paper 03, and the original bounded B-vector
substitution/C_i domain and weak scalar proof for paper 05. Whole decision and norm claims remain pending until their full
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

The [third focused checkpoint](verification/repair-2026-10-31/checkpoint-03.json)
combines fourteen accepted gates with thirty-three exact-type aliases. All
125 local closure source hashes match before and after compilation. The root
selects 719 gates, without a new whole-root build. The general forbidden-family
representation completes `lem:image-cover`, raising the current count to
87 checked; the new finite-profile and arbitrary-policy partial components
retain their explicitly limited supplier scope.

The [fourth focused checkpoint](verification/repair-2026-10-31/checkpoint-04.json)
combines twenty accepted gates with fifty-one exact-type aliases. All 148
local closure source hashes match before and after compilation. The root
selects 725 gates, without a new whole-root build. The full source regularity
adapter raises the register to 88 checked. One expansion gate needed the
same audit-visibility repair as the earlier aggregate: only an empty imported
namespace audit was removed, with all fixed aliases and their actual audits
retained. The prior freeze, failed receipt and exact amendment are preserved.

The [fifth focused checkpoint](verification/repair-2026-10-31/checkpoint-05.json)
combines twenty-seven accepted gates and seventy-three exact-type aliases.
All 180 local closure source hashes match before and after compilation. The
root selects 732 gates; the whole-root build remains separate. The finite
expansion proposition raises the register to 89 checked.

This checkpoint also corrects an integration-layout error in the root module:
the continuation imports are now before the global audit command, in the
module header. No proof or fixed gate changed. A [static layout check](verification/repair-2026-10-31/root-header-layout-check.json)
records the exact move. Earlier focused component checks remain valid, but
did not check this root layout. Whole-root revalidation is now planned in
serialized batches. This does not diagnose the historical CI failures.
