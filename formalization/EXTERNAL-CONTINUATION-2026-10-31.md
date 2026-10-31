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
  also gives actual component permutations and fiber isomorphisms. The later
  complete canonical-cotree result below composes these ingredients.
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
  Concrete flattening and binary expansion complete the source chain below.
  [Evidence](verification/repair-2026-10-31/ForestParseRepresentationCotreeStatementChecks.json).
- **Paper 05, finite-tail collapse facts: checked suppliers.** Actual
  finite-tail norm/increment monotonicity and natural finite-right sum
  calibration support the weak scalar proof. These are not global collapse
  monotonicity and do not replace the original bounded-substitution domain.
  [Tail evidence](verification/repair-2026-10-31/WWFiniteTailMonotonicityStatementChecks.json)
  and [calibration evidence](verification/repair-2026-10-31/WWFiniteNaturalTailStatementChecks.json).
- **Paper 03, `lem:canonical-cotree`: checked in full.** Concrete flattening
  constructs a reduced cotree for every binary parse. Actual connected
  components recover its unique unordered structure, and independent
  occurrence-labelled binary skeletons characterize every graph-isomorphic
  representation. The source-facing conjunction is checked at a fixed type.
  [Whole-lemma evidence](verification/repair-2026-10-31/CanonicalCotreeCompletionStatementChecks.json).
- **Paper 05, `wwsc:thm:weak`: checked in full.** The original closed B-vector
  substitutions and norm-admissible C domains are defined faithfully and
  proved nonvacuous. The exact occurring-support scalar inequality, validity
  and head-freeness of every partial, and validity/head-freeness of the pure
  assembled delta are all proved for every structural policy. The existing
  source abstraction is separately related to delta plus retained head
  closure, rather than silently identified with delta.
  [Whole-theorem evidence](verification/repair-2026-10-31/WWOriginalWeakReplacementStatementChecks.json).
- **Further checked suppliers in this checkpoint:** actual CFG skeleton and
  occurrence-count semantics; precise production flows, support ranks,
  open-context rotation/insertion and initial forests; executable Presburger
  flow/rank formulas and finite count substitutions; and actual sum/product/
  exponential norm estimates and original-domain positivity. A balance-only
  counterexample guards against an insufficient proposed conversion, and is
  not a criticism of the manuscript. No general Presburger or JEP decision
  procedure follows from these supplier records.

## Seventh-checkpoint source completion

The repaired paper 03 chain is now complete: exact effective Parikh
transition formulas, actual Presburger decision and automaton inclusion,
finite ranked-tree ideal decomposition, and the original finite-forest JEP
Boolean decision all have fixed checked targets. The decision takes an
actual finite coded forest family and is equivalent to its original order-JEP
property, without an ideal-cover or decision oracle. Empty cases are included.
These are total symbolic algorithms; no practical runtime claim is made.

Paper 05 now also has the exact first-free and bounded-norm statements,
actual zero-history source assignment, both forward-translation statements,
and the source-class corollary. The latter restricts all internal types and
subtypes, under the inherited ground-free-name context, not merely the result
type. Policy-relative translation does not assert that arbitrary selectors
are computable. Original delta and the abstraction with retained head closure
remain distinct.

The register for this checkpoint contains **189 statements: 99 checked,
2 inherited calculator-package results, and 88 pending**. Paper 03 has all
11 registered statements checked. Paper 05 has 17 of 18 checked; its
counter-bound proposition remains pending.

## Original-source countervaluation bounds

The eighth checkpoint completes paper 05's `prop:counter-bound` on the
actual original-T input domain. A numeric source codec and context-sensitive
typechecker, exact printed-default assignment compiler, refusing scalar and
positive-vector extraction, and ordinal normalization all have genuine
primitive-recursive certificates and semantic correspondence proofs.
The final input predicate is defined independently using typed original
terms and their actual default assignments, rather than compiler outputs.

The checked proposition proves co-recursive-enumerability and the exact
equivalence between decidability and a total computable countervaluation
bound indexed by the original input code. It covers both weak and strict
comparison, independent shared ground variables, unrestricted output/internal
types, and the zero-arity closed test. Invalid numeric codes have an explicit
vacuously true extension; no compiler-image assumption restricts real inputs.
The printed default's right-associated optional box tail is preserved.

This **does not prove decidability or construct a countervaluation bound**.
The source's main open comparison problem remains open. It completes the
formalization of the elementary conditional characterization, not a solution
to that problem.

The current register contains **189 statements: 100 checked, 2 inherited
calculator-package results, and 87 pending**. All 11 registered statements
of paper 03 and all 18 of paper 05 are checked. Remaining work continues on
the other papers; known source-domain issues are not silently repaired.

## Verification environment

This is a fresh checkout. The pinned Lean `v4.32.0-rc1` and Mathlib
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` have been restored using official
upstream caches. No upstream theorem rebuild was used. Local compilation uses
the existing serialized, bounded runner; exact gates and axiom audits are
required before acceptance. A comparator compile alone is not a proof.

CI diagnosis and repair remain deferred. No remote CI pass is claimed.
The new component sources and exact gates were directly compiled. Their
unchanged upstream dependencies used official cached objects. The complete selected root has now passed as recorded below; historical
baseline evidence remains preserved separately. Raw receipt identities, actual axiom logs, source hashes
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

The [sixth focused checkpoint](verification/repair-2026-10-31/checkpoint-06.json)
selects sixty-one accepted gates and checks 171 exact-type aliases. All 312
local source closure hashes match before and after compilation. The root
selects 766 gates; the full historical closure is still being revalidated
separately. Canonical-cotree and weak replacement raise the register to
91 checked.

The [seventh focused checkpoint](verification/repair-2026-10-31/checkpoint-07.json)
selects 152 accepted gates and checks 441 exact-type aliases. All 762 local
source closure hashes match before and after compilation. The root selects
857 gates; this focused pass does not claim a fresh full-root compile.
Eight whole-statement acceptances raise the register to 99 checked. Later
source-frontend work is outside this fixed checkpoint snapshot.

One States component has a disclosed late dedicated manifest: its exact
definitions and targets were already hash-pinned by a successful comparator
receipt before the reported proof draft, but the dedicated manifest and gate
hash were recorded later. The record keeps `candidate_absent_at_freeze=false`,
the earlier comparator hashes and separate source review. Its actual fixed
gate types and axiom closures are checked. This is not represented as a
pristine pre-author gate freeze. An [additive receipt clarification](verification/repair-2026-10-31/WWAdmissibleExpansion-receipt-clarification.json)
also distinguishes an earlier proof compilation from a later gate-only
recompile, preserving the original published evidence unchanged.

[Publication provenance](verification/publication-provenance-2026-10-31.json)
maps local commit identifiers used in some frozen records to public commits
with identical content trees. Manuscript hashes still identify the repaired
source baseline exactly.

No independent human review or priority claim is made.

## Complete selected-root verification

[Root verification evidence](verification/repair-2026-10-31/root-checkpoint07.json)
records the exact selected root, prerequisite compiler rows and axiom audits.
Raw receipt/log references identify hashed locally retained artifacts; those
raw files are not included as public downloads in this checkpoint.

After the seventh focused checkpoint, every one of the 3,076 local root
prerequisites was revalidated at its current source hash, then the actual
root module passed with all 857 selected imports and 2,631 audited namespace
theorems. All 3,077 root-closure source hashes were identical before and
after the root run. This verifies exactly the checkpoint-seven source tree;
later unimported source-frontend work is outside this result.

The first root attempts stopped at the 1,536 MiB and 2,048 MiB RSS guards
during import loading, without a reported theorem failure. A separately
authorized current root-only profile (4,096 MiB heap and RSS caps,
6,144 MiB minimum available memory, unchanged CPU/wall/thread limits) passed
in 2.389 seconds at a peak of 2,603,504 KiB RSS. Both earlier stops are
preserved. This is a current verification profile, not a claim about the
historical profile. No global runner, toolchain or CI configuration changed.

These local observations establish a memory requirement for this selected
root in this environment; they do not diagnose historical GitHub CI failures
or claim a remote CI pass.

## Eighth-checkpoint verification

The [eighth focused checkpoint](verification/repair-2026-10-31/checkpoint-08.json)
selects 168 accepted gates and audits 493 exact aliases, with all 832 local
closure hashes unchanged. The actual updated root also passed with 873
imports, 2,709 namespace theorem audits, and all 3,147 local closure hashes
unchanged. Its separate [root evidence](verification/repair-2026-10-31/root-checkpoint08.json)
records the same expressly authorized current root-only 4,096/4,096/6,144 MiB
profile. The root run took 2.544 seconds and peaked at 2,614,328 KiB RSS.
This includes the completed original-source counter-bound chain. It remains
a local verification result, not a GitHub CI result or a cold upstream rebuild.

## Subsequent algebra and prediction suppliers

The next checkpoint continues other pending source chains without promoting
additional whole statements. For paper 01, the literal root-adjunction
quotient has unique digit representatives, faithful original-group inclusion
and its required root relation. Recursive finite rooted-tree quotients have
the exact digit-sum normal form and all parent equations. The actual infinite
Walker construction and transfinite filtration remain separate obligations.

For paper 14, checked machine suppliers establish exact bounded-prefix
runtimes on actual TM2 and TM0 machines, a primitive-recursive finite
transition-table decoder and bounded simulator, and uniform numeric codes
for the actual tape evaders with exact output/runtime correspondence. These
results do not identify the table numbering with the source's acceptable
numbering, prove a runtime-preserving compiler, or complete source hardness
or membership statements. Those bridges remain explicit work in progress.

The register remains 100 checked, 2 inherited and 87 pending.

The [ninth focused checkpoint](verification/repair-2026-10-31/checkpoint-09.json)
selects those six new suppliers, for 174 gates and 516 exact aliases. All
868 focused closure hashes match before/after. Its [actual root check](verification/repair-2026-10-31/root-checkpoint09.json)
also passed: 879 imports, 2,740 namespace audits, all 3,171 local closure
hashes unchanged, and the same expressly authorized current root-only profile.
It took 2.536 seconds and peaked at 2,613,920 KiB RSS. Later universal-property
and subtree-map work is outside this fixed snapshot. No whole source target
was promoted in this checkpoint.

## Further source-construction links

Paper 01 now also has actual finite-presentation universal properties,
faithful ancestor-subtree maps, coherent stage inclusions, and their concrete
direct limit. Actual decreasing-ordinal nodes have all lower-height children,
with a finite-or-countable ancestor-respecting enumeration; there is no
finite-branching or natural-rank cutoff. Identification with the original
ordinal presentation and its transfinite filtration remain unpaid here.

Paper 14 adds an effective table-to-Partrec code family with exact partial
output semantics, variable finite work alphabets, an exact embedding of the
three-symbol evaders, and fixed-dimension finite transition serialization.
The table-to-Partrec translation does not preserve a claimed source runtime.
Raw binary input/output adapters and acceptable-numbering calibration remain
separate. The source restricts the input alphabet, not the working alphabet.

A paper 12 supplier now gives a finite arity-indexed primitive-recursive
program AST with exact extensional correspondence to Mathlib's primitive
recursive functions and the recursion equations. This is not an executable
compiler from arbitrary extensional functions, nor a primitive-recursive
universal evaluator. The literal source U/u defining-equation registry,
arithmetic provability, Hilbert--Bernays conditions and the self-indexed
knowledge theory still need their actual formal constructions. All six
registered source statements of paper 12 remain pending.

The [tenth focused checkpoint](verification/repair-2026-10-31/checkpoint-10.json)
selects eleven additional suppliers: 185 gates, 555 exact aliases, and 912
unchanged local closure hashes. Its [actual root verification](verification/repair-2026-10-31/root-checkpoint10.json)
passed with 890 imports, 2,782 namespace audits and all 3,215 local closure
hashes unchanged. The expressly authorized current root-only profile was
unchanged; the run took 2.54 seconds at a peak of 2,616,912 KiB RSS. The
register remains 100 checked, 2 inherited and 87 pending; no whole statement
was promoted. Later source-presentation and limit-universal work is outside
this fixed snapshot.

## Complete original Walker filtration lemma

Paper 01's `lem:walker-filtration` is now checked in full on the literal
free-abelian quotient generated by every finite decreasing-ordinal node.
For each countable ordinal and prime p, the final source-facing conjunction
proves countability, p-primary torsion and reducedness; unique finite
p-digit expressions; the actual transfinite p-filtration at every ordinal;
and all terminal conclusions. These include the root-generated cyclic group
of order p, the zero next stage, and the cyclic group of order p squared at
the specified predecessor stage. No normal-form, support, enumeration,
filtration or source-isomorphism assumption is left as a hypothesis.

The full node enumeration admits arbitrary countable ordinal height and
branching. Actual finite quotient extensions, subtree embeddings, a direct
limit and a generator-tracking isomorphism establish the original source
presentation before its support and filtration arguments. Independent source
review preceded the final exact target freeze and proof. The final evidence
discloses a subsequent reviewer-label-only provenance edit; it does not claim
that unavailable original metadata bytes were retained or reconstructed.

This raises the register to **101 checked, 2 inherited and 86 pending**.
Paper 01 has 5 of 12 registered statements checked. Its remaining Scott
complexity classification and difference-spectrum obligations are not
inferred from the Walker construction.

Further scoped work continues on source machine support/coding and the
knowledge paper's actual PR registry, quantified defining equations and
existing Hilbert derivations. Those components do not by themselves complete
source runtime/numbering calibration, arithmetic provability or Löb's theorem.

The [eleventh focused checkpoint](verification/repair-2026-10-31/checkpoint-11.json)
selects 204 accepted gates and audits 614 exact aliases, with all 1,045 local
closure hashes unchanged. The [actual updated root](verification/repair-2026-10-31/root-checkpoint11.json)
passed with 909 imports, 2,886 namespace audits and all 3,291 local closure
hashes unchanged. Its current root-only bounded profile was unchanged;
the run took 2.639 seconds and peaked at 2,633,696 KiB RSS. Only the complete
Walker filtration lemma was promoted; all other new components retain their
explicit supplier scope. Later call-congruence/compiler work is outside this
fixed snapshot. No GitHub CI result is claimed.
