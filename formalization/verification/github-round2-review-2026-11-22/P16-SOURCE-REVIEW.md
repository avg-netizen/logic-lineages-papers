# Paper 16 source correspondence review

Review date: 2026-11-22 (America/Chicago).

Reviewed publication delta: `a14a936772e01363795c919c106607fdad368f8c` to
`1cd1734feb2b64c5a9936b2b5e8649f9b2f3889c`. Line references below refer to
the latter source snapshot. Paths beginning `LogicLineages/` or
`verification/` are relative to `formalization/`; manuscript paths are
relative to the repository root.

Short Lean basenames in section 1 refer to
`LogicLineages/PersistentMarking/`. In sections 2–4, native basenames refer
to `LogicLineages/NativeModule/PersistentMarking/`; the shared generic
`OrdinalRealizationTargets.lean` and `OrdinalNativeIterationTargets.lean`
remain under `LogicLineages/PersistentMarking/`. Short `HANDOFF.md`, `opusA/`,
and `opusB/` references refer to
`verification/local-fable-pair-2026-11-22-round2/`.

## Verdicts

| Item | Statement-to-source verdict | Consequence |
|---|---|---|
| #1449, corrected `lem:structural-interpretation` | No material mismatch found in the paper's finite, typed, covered setting. The fixed-point qualification is present, and the two substitution contracts cover the locally nameless operations used by the source. | The numbered promotion is justified against the corrected TeX source. It does not rehabilitate the old unqualified application clause. |
| #1446, `NativeIteratorRealizesFullPrefix` | Matches printed `thm:iteration`, including the literal iterator, all semantic functions, countable ordinal indices, and the entire prefix at limits. | No remaining statement-correspondence obstruction was found. Register promotion remains a separate action; this review makes none. |
| #1447, `NativeRealizationClosure` and `NativeLambdaRealization` | The three closure clauses match. The lambda result is a conditional abstraction rule, not a stated general structural fundamental lemma for open typed terms. | Keep the numbered lemma pending while its final sentence retains the broader terminology without an explicit interpretation. |
| #1448, native ranks and rank comparison | The targets use ranks of the actual relations. Unconditional public assemblies discharge the accessibility/countability requirements of their component lemmas. | Supporting acceptance is appropriate. These results do not establish the Bachmann–Howard upper bound or the internal ID1 accessibility proof. |

No new blocking implementation defect was found in this scope. The lambda
sentence is an existing, explicitly disclosed correspondence boundary, not a
new proof failure. Native proof validity, axiom closure, and module-copy
provenance are separate gates; this review examines the definitions and
propositions rather than repeating those gates or a full proof-body audit.

## 1. Corrected structural interpretation: #1449

The current manuscript qualifies precisely the clause that failed at the
bottom family. `16-persistent-marking-termination-ordering/sections/decision.tex:149-159`
says that full-application interpretation holds at a fixed point of the
constructor operator, while monotonicity, weakening, and substitution remain
unqualified by fixedness. The revised adequacy passage at `decision.tex:232-238`
does not invoke full-application interpretation during the finite-stage
soundness induction. It instead uses the hereditary relation on whole tuples
and reserves full application for the stable family. These are the two sites
identified in the correction record.

`LogicLineages/PersistentMarking/StructuralInterpretationCorrectedTargets.lean:20-24`
is exactly the conjunction of `InterpretationLaws`, `FreeSubstitution`,
`BoundSubstitution`, and `FixedApplication`. Its scope matches those four
claims as follows.

* `ProtectedSpineLawTargets.lean:40-54,77-81` supplies value and helper validity,
  weakening/naturality, and monotonicity in valid assignments and full tuple
  inputs at a fixed retained constructor family. The prefix-closed environment,
  typing, and coverage premises express the finite domains and coherent
  families set up at `decision.tex:9-20,41-96`. This is not a claim about arbitrary
  untyped syntax or malformed finite codes.
* `ProtectedSpineSubstitutionTargets.lean:8-21` relates interpretation of a
  source to interpretation after typed free substitution. The substituted
  image's abstract value is the required environment value. `FreeSubstitution.lean:7-23`
  shifts an image under retained binders and does not recursively substitute
  inside that image, which is the capture-avoiding operation of the locally
  nameless representation.
* `ProtectedSpineBoundTargets.lean:8-29` handles simultaneous removal of a
  block of bound variables while retaining the inner binders. The restriction
  `k = l` and `k ≤ kept.length` in `RetainedProtection` preserves the distinction
  between protected binders consumed by the original spine and variables whose
  substitution images may supply a full application table. It does not silently
  identify application after substitution with application before substitution.
* Both substitution results return `Agreement`.
  `ProtectedSpineAgreementTargets.lean:11-17` includes equality of the helper's
  full tuple calls as well as equality of interpreted values. Consequently
  the concrete-substitution environment can be transported to interpretation
  of the substituted source before applying the fixed-point application law.
* `ProtectedSpineFixedApplicationTargets.lean:36-41` explicitly assumes
  `step S E H M = M`, typed source and arguments, and the finite coverage
  conditions. Its equality is with `concreteOutput (apply q args)`;
  `concreteOutput` maps `none` to the entire bottom code at lines 15-19.
  Thus the asserted application law includes undefined outcomes rather than
  assuming successful application.

The `EmptyContext` premises in the substitution and application targets do
not mean that all source terms are closed. The syntax distinguishes named
free variables from de Bruijn bound indices (`SpineSyntax.lean:5-13`). An empty
bound context excludes dangling bound indices, while named free variables
remain available. In particular `ProtectedSpineEnvironment.lean:33-43` assigns
an unassigned free name its literal variable value. This accounts for the
paper's free names and observation ports; it is not a restriction to the
closed-native domain of the ordinal section.

**Conclusion:** #1449 is justified for the corrected source under its existing
finite typed setup. There is no residual requirement that the constructor
family be the *least* fixed point for this application law; the checked target
and the lemma both require only a fixed point. The stage argument now respects
that distinction. The counterexample remains a boundary on the earlier
statement and is not erased by this acceptance.

The frozen pre-correction source map at
`verification/local-fable-pair-2026-11-22-round2/root/P16-STRUCTURAL-INTERPRETATION-SOURCE-MAP.md:8-23`
records the earlier unedited manuscript and an unexamined substitution
question. The end-of-round handoff at `HANDOFF.md:76-82` and accepted record
`verification/new-paper-set-2026-11-18/accepted/1449-p16-lem-structural-interpretation.json:9-27`
record the later correction. This review supplies the focused substitution
and corrected-wording check that the latter record says had not yet occurred.

## 2. Native iteration: exact domain and quantifiers

`LogicLineages/NativeModule/PersistentMarking/NativeOrdinalIterationTargets.lean:24-28`
has the quantifier order

```text
for every signature S, there is native well-foundedness wf,
for every semantic finite type A, there is iterate,
such that for every f and x the full-prefix orbit equations hold,
and the literal typed iterator realizes iterate.
```

The well-foundedness witness is an existential conclusion, not an assumption
left to callers. The source relation is also fixed:
`NativeIteratorStrictTargets.lean:10-16` defines `NativeBelow target source`
as `ConfinedPair.Strict S source.val target.val` on closed native terms of one
literal type. `NativeOrdinalRealizationTargets.lean:23-26` uses precisely that
carrier/relation and ordinary native application.

The semantic domain at
`LogicLineages/PersistentMarking/OrdinalRealizationTargets.lean:13-27` is the
countable ordinals at base type, the full function space at arrows, and
pointwise suprema. This matches `ordinals.tex:390-391,423-432`; it is not a
monotone-function restriction. `OrdinalNativeIterationTargets.lean:10-26`
uses every ordinal strictly below the limit as its index set, with zero,
successor, and nonzero-limit equations. Its unique-orbit proposition fixes
the meaning of the existential semantic `iterate`. No cofinal-subsequence
replacement has entered the target.

The iterator shape and typed term at `NativeOrdinalIterationTargets.lean:15-18`
have type `ι → (A → A) → A → A`. The literal term correspondence in
`verification/local-fable-pair-2026-11-22-round2/opusA/P16-THM-ITERATION-CORRESPONDENCE.md:21-34`
matches the three binders, recursor, discarder, eraser, and bound indices of
the displayed term at `ordinals.tex:452-456`. The realization quantifiers
require closed realizers for the semantic arguments, as does the definition
at `ordinals.tex:430-432`; neither statement asserts that every set function
has a closed realizer.

**Conclusion:** `NativeIteratorRealizesFullPrefix` matches the printed theorem
at `ordinals.tex:467-469`. The countable-ordinal domain is the paper's stated
domain. The unresolved lambda sentence does not block this correspondence:
the iterator uses strict backward transport and the countable-supremum
clause, with the finite beta chain supplied by
`NativeIteratorStrictTargets.lean:20-26`.

## 3. Realization: the lambda sentence remains a promotion boundary

**Severity: P2 for an unrestricted promotion of the numbered lemma; already
disclosed and correctly left pending.**

`ordinals.tex:434-439` states the three closure clauses and then says that the
typed lambda fundamental lemma holds. The first three clauses match
`NativeOrdinalRealizationTargets.lean:28-33` and the definitions at
`OrdinalRealizationTargets.lean:44-59`: backward transport along a strict edge,
downward closure in semantic value, and one fixed term realizing a nonempty
countable family and its pointwise supremum.

The direction of strict transport is explicit in Lean: if `source` is
strictly above `target` and `target` realizes a value, then `source` realizes
it. This is the backward transport used by the manuscript at
`ordinals.tex:447-449,478-494`. The phrase “strict predecessor” should not be
read as permission to lower a realizing term's rank.

`NativeOrdinalRealizationTargets.lean:35-44` proves this conditional
abstraction rule: for a closed native lambda, if every closed native argument
realizing a semantic input yields a substituted body realizing the prescribed
output, then the lambda realizes the function. The universal body's
realization is a hypothesis. There is no semantic interpretation of arbitrary
open native syntax in this target and no theorem that all typed terms under
realizing substitutions realize their denotations. This agrees with the
limitations explained in `opusA/P16-LEM-REALIZATION-CORRESPONDENCE.md:79-112`
and `opusB/P16-GAP-MAP.md:34-54`.

The manuscript's proof at `ordinals.tex:446-449` establishes the abstraction
rule and its iteration along finite strict beta chains. It does not supply
the additional semantic denotation, constant cases, and structural theorem
that a general fundamental lemma would require. Iterating strict-backward
closure along a finite chain does not supply those missing clauses.

**Smallest correction if the intended claim is the checked rule:** replace
the final sentence with an explicit abstraction implication, for example:

> For a closed native abstraction, if substituting every closed realizing
> argument into its body realizes the corresponding function value, then the
> abstraction realizes that function. Realization also transports backward
> along every finite chain of native strict beta steps.

If the intended claim is a general typed fundamental lemma, it needs its own
precise denotation and target. This review does not choose that mathematical
scope or change the manuscript. The #1447 supporting record accurately names
the one-binder abstraction rule and makes no numbered promotion.

## 4. Ranks and inherited accessibility parameters

The component targets are deliberately conditional where ranks need an
accessibility witness. `NativeRankTargets.lean:15-45` defines native and full
confined ranks as `Acc.rank`, then states recurrence, strict-edge decrease,
restriction domination, and successor-witness laws with the appropriate
`Acc` arguments. The countability component also takes
`ClosedNativeCountability`. These are real hypotheses of those component
statements, not independent proofs of global well-foundedness.

The public assembly removes those obligations:
`NativeRankGlobalTargets.lean:14-27` returns native and full confined
well-foundedness witnesses for every signature and type, then states
countability, domination, recurrence, strict decrease, and the successor
witness for every closed native term. At
`NativeRankUnconditionalChecks.lean:17-21`, the three suppliers are the accepted
closed-native well-foundedness, full confined well-foundedness, and syntax
countability theorems. Thus the public `exact_ActualClosedNativeRanks` does
not inherit an undischarged well-foundedness or countability premise. This
matches the rank definition and observations at `ordinals.tex:337-342`.

The additional comparison wrapper has the same distinction.
`NumberedWindowConfinedRankDominanceTargets.lean:18-21` is conditional on two
accessibility witnesses for a guarded term. Its public
`OriginalInitialQuoteRankDominance` at lines 23-29 starts with only a typed
ordinary term, returns the guarded representative with the same source
syntax, and supplies both symbolic and fixed-window numerical
well-foundedness witnesses before comparing their actual ranks. Its numerical
object is `quote start` in the stated fixed-window relation. It does not
identify that rank with an ID1 inductive norm.

**Conclusion:** #1448 is accurately supporting-only. No source-level argument
here closes the rank-equals-norm bridge, the internal ID1 accessibility
theorem, or Pohlers's ordinal bound. The pending status of `thm:upper` in
`HANDOFF.md:83-85` and `opusB/P16-GAP-MAP.md:128-157` is warranted. An eventual
identification of `quote start` with the manuscript's translation remains
part of that separate comparison, not an implication of this review.

## Evidence and publication boundaries

The source review relies on the recorded exact native gates for #1443/#1449,
#1446/#1447, and #1448; it introduces no replacement proof-validity receipt.
The module-copy transformation audit is separate. The accepted names retain
their original namespaces while their native evidence uses the
`LogicLineages/NativeModule/` module paths.

The correction record explicitly says `paper.pdf` was not rebuilt
(`#1449:18`, `HANDOFF.md:79-80`). The structural verdict concerns the corrected
TeX and its recorded checksum; it is not a claim that the existing PDF already
contains the correction. No source target, proof, register entry, or accepted
record was changed by this review.
