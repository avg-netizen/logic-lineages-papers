# External continuation after the manuscript repairs

## Current verified snapshot: checkpoint 17

**116 checked, 2 inherited, 71 pending, out of 189 registered statements.**
The combined Lean root passes locally with 1,037 selected imports and 3,230
namespace theorem audits. Historical sections below retain the limits and
counts of their own checkpoints. No GitHub CI pass is claimed.

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

## Direct sums, numeral certificates and numeric code interfaces

The next supplier checkpoint proves actual transfinite p-filtration
commutation with arbitrary direct sums and constructs the source lower
reservoir and odd/even terminal families. Countability, reduced p-primary
properties where stated, terminal group equivalences and zero upper stages
are checked. No effectiveness for arbitrary countable ordinals, exact length
for all r, complete Ulm table or Scott complexity is inferred.

Paper 12's generated finite PR theory now has actual positive AND negative
Hilbert numeral certificates in the existing calculus. Negative certificates
are proofs of negated wrong-output equalities, not merely external semantic
non-derivability. These results still concern the generated PR theory, not
the named source Base, its self-indexed knowledge theory or internal
provability/Hilbert--Bernays/Löb properties. The old total ground-diagram
theory and full-language revision grounds are not silently identified with
a new finite defining theory.

The machine lane adds actual sequential Code and continuation codecs and
primitive-recursive interfaces, finite-table execution with both directions
of encoded-stack output semantics, and a proved leading-one binary sentinel
layout. Static layout is not a prefix-machine runtime or a complete
raw-binary compiler. Uniform numeric-index compilation and the input/output
transducers remain separate until their actual proofs are accepted.

These are supplier acceptances only; the register remains 101 checked,
2 inherited and 86 pending.

The [twelfth focused checkpoint](verification/repair-2026-10-31/checkpoint-12.json)
selects 218 gates and audits 659 exact aliases, with all 1,121 focused closure
hashes unchanged. Its [actual selected-root check](verification/repair-2026-10-31/root-checkpoint12.json)
passed with 923 imports, 2,974 namespace audits and all 3,347 local closure
hashes unchanged. The current root-only profile was unchanged; the run took
2.437 seconds and peaked at 2,636,104 KiB RSS. Fourteen scoped suppliers were
added, with no whole-statement promotions. Later Ulm additivity, continuation
interfaces and prefix-machine candidates are not part of this fixed snapshot.

## Invariant tables and explicit raw machine behavior

Further paper 01 suppliers prove actual direct-sum Ulm-layer additivity,
the reservoir's cardinal rank table and the full odd/even source invariant
tables. The constructed groups have the proved nature, exact first-zero
lengths under positive multiplicity, and distinct-multiplicity nonisomorphism
via actual Ulm invariance. This does not supply the Scott-complexity
classification used by the source difference-spectrum theorem.

Further machine suppliers provide explicit actual label payload codecs and
primitive-recursive interfaces, a separately frozen machine with a pinned
prefix initial state, exact singleton output layout and epilogue, and
one-way raw-binary correctness for singleton-binary source results. They do
not establish arbitrary partial-binary equivalence, acceptable numbering or
a runtime-preserving general compiler. Earlier unaccepted attempts with an
unvalidated initial state or mixed codec instances remain separate; failed
definitional checks were not represented as semantic counterexamples.

The knowledge lane proves a padded concrete PR registry whose internal
headers do not collide with the existing named source headers, with actual
AST witnesses for the specific paid source dispatchers. Padding alone does
not establish a named alias theory, adequate Base, internal provability or
full-language model correspondence. All six paper 12 statements remain
pending, and the global register stays 101 checked, 2 inherited, 86 pending.

The [thirteenth focused checkpoint](verification/repair-2026-10-31/checkpoint-13.json)
selects 231 gates and audits 703 exact aliases over 1,296 unchanged local
source hashes. Its original normal-profile invocation stopped at the RSS
guard without a proof error. One explicitly authorized focused-only retry
with 2,560 MiB heap, 2,048 MiB RSS and 3,072 MiB minimum-free limits passed
in 3.248 seconds at 1,712,076 KiB peak RSS. The original stop and identical
source snapshots are retained; no default runner limit changed.

The [actual selected root](verification/repair-2026-10-31/root-checkpoint13.json)
also passed: 936 imports, 3,041 namespace audits and all 3,399 local closure
hashes unchanged, in 2.285 seconds at 2,645,020 KiB peak RSS under the
previously authorized root-only profile. No GitHub CI result is claimed.

## Algebraic classification and named-theory correspondence

The actual algebraic Ulm theorem is now checked: countable reduced
p-primary groups are additively isomorphic exactly when their actual
transfinite Ulm ranks agree, and finite height-preserving maps extend.
Countable stabilization and zero-stage limits are constructed, not assumed;
finite extensions and a coherent total isomorphism are proved. This is NOT
the paper's Scott-complexity classification or its difference-spectrum
theorem. The countability and infinitude bridges for the literal gamma-indexed
Walker constructions are also checked. A proof-only import narrowing allowed
the countable-isomorphism supplier to pass normal bounds after its preserved
resource stop; conditional heavier permission was not used for that supplier.

The knowledge lane now has literal named U/u calibration, a new finite
named-alias theory with explicit model and actual named positive/negative
numeral derivations, and literal diagonal fixed-point proofs in that new
theory. None imports old total-diagram axioms or identifies full-language
revision grounds. Internal uniform proof-checker closure, actual Base
adequacy and Hilbert--Bernays/Löb obligations remain separate.

The program lane proves a single fixed finite sequential universal-program
existential with exact partial natural-output semantics after a genuine
primitive-recursive sentinel conversion. No program is chosen separately
for each index. Numeric prefix assembly/execution and the exact singleton
output observer are checked; this checkpoint does not yet complete the
validating machine or a uniform raw-binary index translation.

The [fourteenth focused checkpoint](verification/repair-2026-10-31/checkpoint-14.json)
selects 246 gates and audits 764 exact aliases over 1,427 unchanged local
source hashes. The explicitly authorized focused-only 2,560/2,048/3,072 MiB
profile passed in 3.613 seconds at 1,713,540 KiB peak RSS. The
[actual selected root](verification/repair-2026-10-31/root-checkpoint14.json)
passed with 951 imports, 3,070 namespace audits and all 3,459 local closure
hashes unchanged, in 2.54 seconds at 2,645,360 KiB peak RSS under the
previous root-only profile. These are local checks; defaults and CI remain
unchanged. No whole statement was promoted: 101 checked, 2 inherited,
86 pending. Later validator and attach-exit components are outside this
fixed snapshot.

## Seven further whole-source acceptances

The fifteenth checkpoint completes seven numbered source statements:

- Paper 01, `lem:infinite-divisible-bf`: the original group-language odd,
  even and nonzero-limit tuple comparisons from actual infinite
  divisible-part ranks, without extra family, cut-socle or extension-oracle
  premises. Actual finite-response algebra and ordinal induction are paid.
- Paper 09, `lem:addition` and `lem:sort`: full default-policy typed source
  equations, unique fresh addition witnesses, the S/I definition of one,
  logarithmic shared binary addition DAGs, actual S pair coding and an
  explicit primitive-positive sorting graph, preserving shared inputs.
- Paper 14, `lem:robust`, `lem:membership`, `prop:threshold` and
  `prop:hardness`: the actual raw-tape robust rule for arbitrary prediction
  histories; recursive membership and threshold matrices with strict
  physical runtime; and both hardness clauses, with one and the same
  total-predictor family for the diagonal threshold, literal infinite
  measure and every sufficiently high fixed level. The original-list
  hypotheses are exactly the source-stipulated effective evaluator,
  per-entry primitive recursion and coverage properties.

The source addition proof remained under normal resource bounds after
factoring and symbolic finite-tail comparison avoided astronomical closed
control evaluation. Historical stops remain disclosed. Two unaccepted
measure/membership target drafts had unintended arrow/iff grouping; fresh
explicitly parenthesized scopes were separately frozen and verified. Those
drafts were not silently amended or counted as accepted.

The [fifteenth focused checkpoint](verification/repair-2026-10-31/checkpoint-15.json)
selects 284 gates and audits 869 exact aliases over 1,626 unchanged local
source hashes. Its scoped focused profile passed in 3.806 seconds at
1,735,264 KiB peak RSS. The [actual selected root](verification/repair-2026-10-31/root-checkpoint15.json)
passed with 989 imports, 3,143 namespace audits and all 3,617 local closure
hashes unchanged, in 2.539 seconds at 2,653,904 KiB peak RSS under the
root-only profile. The pre-check registry amendment adding the seventh
whole label is preserved; no proof/check boundary was changed mid-run.
No CI or default runner configuration was changed.

This snapshot does not include later collision/aggregation/chain results,
actual third-jump completeness, or final prediction degree endpoints. Their
subsequent acceptance is recorded only in later checkpoints.

## Seven additional whole-source endpoints

Checkpoint 16 completes paper 01's full `lem:terminal-deletion`, including
actual quotient invariants, retained terminal group, exact length and
reducedness, the retained-tuple odd comparison, and the original terminal
back-and-forth hypothesis implying the even comparison. No finite-lifting
or infinite-socle oracle remains as an extra hypothesis.

Paper 09 adds the entire six-eraser collision lemma, conjunction aggregator
and one-final-abstraction unary-chain lemma. These use actual full default
assignments and shared source valuations, not hypothetical scalar/head
interfaces. The later Boolean compiler's polynomial-DAG and general observer
obligations remain separate.

Paper 14 now has all nine registered source statements checked. The new
endpoints are the complete original-measure classification, finite-value
lemma for lists covering all computable functions, and complete canonical
least-index-list classification. Actual third-jump complement normal forms
and actual second-to-third inclusion discharge the degree dependencies;
there is no completeness or oracle-decision premise. Promise-respecting
upper/lower algorithms and the source infinity/finite encoding are explicit.
The canonical list is not treated as uniformly computable, nor supplied an
infinite-level predictor.

The third-jump normal-form bundle uses a disclosed additive metadata
normalization: its original human-readable freeze and intended exact gate
were retained before the proof, independently checked using filesystem
chronology and comparator records. The original freeze contained no inline
UTC timestamp. Later machine-readable linkage is explicitly post-candidate;
no earlier timestamp text or new pre-proof event is invented. Hash-linked
original artifacts remain externally retained rather than publicly included.
The intended gate text and final mathematical source hashes match exactly.

The [sixteenth focused checkpoint](verification/repair-2026-10-31/checkpoint-16.json)
selects 318 gates and audits 937 exact aliases over 1,855 unchanged local
source hashes. Its scoped focused profile passed in 4.113 seconds at
1,764,388 KiB peak RSS. The [actual selected root](verification/repair-2026-10-31/root-checkpoint16.json)
passed with 1,023 imports, 3,201 namespace audits and all 3,761 local closure
hashes unchanged, in 2.694 seconds at 2,705,180 KiB peak RSS under the
root-only profile. Thirty-four selected records are included; later work is
excluded from this snapshot. The register is now **115 checked, 2 inherited,
72 pending**. No GitHub CI result is claimed.


## Checkpoint 17 — absolute observer and scoped Scott suppliers

The complete paper 09 `lem:absolute` is now checked against the strengthened
pre-proof comparator. It covers actual sources in all-ground contexts with
arbitrary output and internal types, the literal-zero closed anchor, a uniform
computable numeric evaluator on the unchanged open-source code/all-one tuple,
and actual fresh ground observations with a shared arithmetic witness formula.
No head-agreement, injectivity or evaluator-correctness premise is assumed.
The final gate is `SourceAbsoluteObserverStatementChecks.fullAbsoluteObserver`
(in its `Source.AbsoluteObserver` namespace).

The other thirteen selected components remain scoped suppliers. In particular,
actual unrestricted Scott upper bounds at zero cuts and bounded tails are not
exact Scott-complexity classification. Actual bounded-tail categoricity,
finite direct summands, transfinite relativization and Ulm descriptors supply
mathematics rather than semantic formula leaves or classification oracles.
The numeric ground-closing transformation is primitive recursive in the
original codec. Source 12 certificate modus-ponens/generalization operations
do not establish a source Base/DCB presentation or internal HB/Lob principles.

The [seventeenth focused checkpoint](verification/repair-2026-10-31/checkpoint-17.json)
selects 332 gates and audits 965 exact aliases over 1,993 unchanged local
source hashes. The scoped focused profile passed in 4.111 seconds at
1,770,468 KiB peak RSS. The [actual selected root](verification/repair-2026-10-31/root-checkpoint17.json)
passed with 1,037 imports, 3,230 namespace audits and 3,823 unchanged local
closure hashes, in 2.537 seconds at 2,711,016 KiB peak RSS. The explicitly
authorized focused/root profiles preserve CPU, wall-time and single-thread
guards; defaults and CI were not changed. Fourteen records were fixed in the
snapshot; later acceptances, including the finite-terminal-deletion supplier,
are excluded. The registry is **116 checked, 2 inherited, 71 pending**. No GitHub
CI result is claimed, and private original third-jump metadata remains excluded.
