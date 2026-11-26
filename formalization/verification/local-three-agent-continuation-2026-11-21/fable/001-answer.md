# PackedLeastOpen: proposed target interface and proof plan (turn 1, read-only)

Nothing here has been compiled or run; every name below was read from the current sources. I read `RELEASE.md`, `CONTROL.json` and lines 1–938 of `AGENTS.md` (the two current release sections; the remaining ~775 lines are older historical releases I did not open).

Two paths in the brief differ from disk:
- **`InternalGraphCompositionSupportProof.lean` does not exist.** The helpers live in `InternalControlGraphSupportProof`, `InternalAcceptanceSupportProof` and `InternalGraphCompositionFunctionalityProof`.
- **The manuscript** is at `16-persistent-marking-termination-ordering/sections/ordinals.tex` (no `manuscript` prefix). The relevant clause is lines 70–76 (finite, effectively enumerable classes; least-code representatives).

## 1. Proposed source

`NumberedWindowInternalSparsePackedLeastOpenDefinitions.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpen
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed packedLeastProgram)

/-- Successful output of the unchanged physical packed least program on
the literal tape [ctx,ty,seed]. The successor tag is the only success test. -/
def leastGraph {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α) : Formula α :=
  programGraph (packedLeastProgram C X W s) (suc selected) ![ctx,ty,seed]

/-- One physical tape in all three graphs' inputs. The pool is the actual
output of the same members program; the candidate is the same selected term. -/
def poolOccurrenceRow {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected contextPayload pool : OTerm α) : Formula α :=
  programGraph contextOption (suc contextPayload) ![ctx,ty,seed] ⊓
    (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ memberGraph pool selected)

/-- Two genuine object quantifiers: context payload outermost, then pool.
The free terms are lifted past both binders, so neither can be captured. -/
def poolOccurrence {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α) : Formula α :=
  let lift : OTerm α → OTerm ((α ⊕ Fin 1) ⊕ Fin 1) :=
    fun t => (t.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl
  existsOne (existsOne (poolOccurrenceRow C X W s (lift ctx) (lift ty) (lift seed) (lift selected)
    (.var (.inl (.inr 0))) (.var (.inr 0))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpen
```

`NumberedWindowInternalSparsePackedLeastOpenTargets.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen

/-- Arbitrary programs, settings, context and open terms. Successful
physical packed least yields, in the same calculus and context, an
existential nonzero context tag, the computed member pool on the same
tape, and occurrence of the same selected term in that pool. No
calibration, validity, decoded list or semantic premise. Occurrence only:
not parser inversion, round ancestry, RawMatching or least semantics. -/
def ExactOpenPackedLeastPoolOccurrence : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α),
    Nonempty (Derivation body Γ
      ((leastGraph C X W s ctx ty seed selected).imp
        (poolOccurrence C X W s ctx ty seed selected)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
```

Design choices for the prescope reviewer:
- **Implication at arbitrary `Γ`.** This matches #732 and `ExactOpenRawMinimumParsedOccurrence`, and is interderivable with the rule form by `implicationIntroduction`/`implicationElimination`.
- **Binder encoding.** Nested `existsOne` with double `relabel Sum.inl` follows `hasPreimage` and `goodState`, so the existing `liftTermSubst`/`existsEmbeddedSubst` lemmas apply.
- **Literal tapes.** `![ctx,ty,seed]` is written inline rather than behind an `abbrev`, so `tripleInputsRename` matches syntactically.
- **Narrow imports.** Only `PackedLeastDefinitions` is imported, not `PackedLeastTargets`, so no numeric calibration module enters the closure.

## 2. Sources and dependencies

| Use | Actual name | File |
|---|---|---|
| Program under test | `packedLeastProgram`, `contextOption`, `membersAtSeed`, `minimumAtMembers` | `NumberedWindowInternalSparsePackedLeastDefinitions` |
| Occurrence graph | `memberGraph`, `selectedOccurs` | `NumberedWindowInternalSparseScratchMembershipTargets` |
| #732 | `exact_OpenScratchMinimumOccurs` | `NumberedWindowInternalSparseScratchMembershipOpenChecks` |
| Template | `reject`, `present`, `recover`, `occurrenceRename`, `occurrenceInstance` | `NumberedWindowInternalSparseRawMinimumOccurrenceOpen{Branches,Syntax}Proof`, `…OpenChecks` |
| Branch inversion | `zeroBranchElim`, `successorBranchElim` | `ID1Completion/InternalAcceptanceBranchProof` |
| Composition inversion | `programCompositionCases` (fallback `programCases` + `compositionRecover`) | `ID1Completion/InternalAcceptanceSupportProof` |
| Functionality, transport | `valueUnique`, `programRename` | `ID1Completion/InternalControlGraphSupportProof` |
| Option case split | `optionGraphCases` | `NumberedWindowInternalFreshProbeProof` |
| Zero branch value | `zeroConstantValue` (generic arity) | `ID1Completion/InternalLessThanSupportProof` |
| Contradiction | `sucNeZeroApply`, then `Derivation.explosion` | `ID1Completion/InternalTagArithmeticSupportProof` |
| Context renaming | `renameInto` | `ID1Completion/InternalGraphCompositionFunctionalityProof` |
| Tape renaming | `tripleInputsRename`, `binaryInputsRename` | `NumberedWindowInternalSparseFieldParserOpenSyntaxProof` |
| Member renaming | `graphRename` | `NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof` |
| Binder syntax | `existsRename`; `existsEmbeddedSubst`, `liftTerms`, `liftTermSubst`; `programSubst`; `conjunctionRename`/`conjunctionSubst`; `bindEmbedding`, `bindTerm`, `liftBind`, `varBind`, `sucSubst`, `zSubst`, `sucRelabel` | `InternalDerivationRenamingSyntaxProof`, `InternalComputabilityApplicationSyntaxProof`, `InternalRawListRecursionSyntaxProof`, `InternalRecursionGraphStepSyntaxProof`, `InternalRecursionClosureSyntaxProof`, `InternalTagArithmeticSyntaxProof` |
| Two-binder introduction precedent | `goodIntro`, `goodRename` | `NumberedWindowInternalSparseRawTickShapeSyntaxProof` |

## 3. Proof plan and obligations

Three new proof files, all with `attribute [local irreducible] programGraph`.

**`…PackedLeastOpenSyntaxProof`** (pure syntax, no derivations except S7)
- **S1 `tapeSubst`**: substitution distributes over `![a,b,c]`.
- **S2 `leastRename`**: `(leastGraph … ctx ty seed j).relabel k = leastGraph … (ctx.relabel k) …`, by `programRename`, `tripleInputsRename`, `sucRelabel`.
- **S3 `memberSubst`**: local re-proof (see missing helpers below).
- **S4 `rowRename` / S5 `rowSubst`**: for `poolOccurrenceRow` in all six term arguments.
- **S6 `occurrenceUnfold`** (`rfl`) and **`occurrenceRename`**: `existsRename` twice, `rowRename`, `Term.relabel_relabel`, `rfl`, as in `goodRename`. This is the capture-avoidance obligation.
- **S7 `occurrenceIntro`**: from a derivation of `poolOccurrenceRow … u pool`, two `Derivation.existentialIntroduction` steps (`emb u`, then `emb pool`), justified by the instance equations `outerInstance` and `innerInstance`, as in `goodIntro`.

**`…PackedLeastOpenBranchesProof`**
- **B1 `reject`**: given `contextOption z tape` and `leastGraph`, `zeroBranchElim contextOption (constantZero 3) (minimumAtMembers C X W s)` gives `constantZero 3` with output `suc j`. `valueUnique` against `zeroConstantValue` gives `eqn (suc j) z`; `sucNeZeroApply` and `explosion` close it.
- **B2 `selectedMinimum`**: given `contextOption (suc u) tape` and `leastGraph`, `successorBranchElim` gives `programGraph (minimumAtMembers C X W s) (suc j) tape`.
- **B3 `present`**: `programCompositionCases scratchMinimum (fun _ : Fin 1 => membersAtSeed C X W s)` on B2 yields an eigen-tuple `ys`. It gives `scratchMinimum (suc j') ys` and `membersAtSeed … (ys 0)` on the renamed same tape, so the pool is `ys 0`.
  - Rewrite `ys = ![ys 0]`, apply #732 and `implicationElimination` to get `memberGraph (ys 0) j'`.
  - Rename the known context graph along the same map, form the conjunction, and finish with S7.

**`…PackedLeastOpenChecks`**
- **`recover`**: `optionGraphCases contextOption ![ctx,ty,seed] (poolOccurrence …)`, with `occurrenceRename`, `leastRename` and `renameInto` in each branch, dispatching to B1 and B3.
- **`exact_OpenPackedLeastPoolOccurrence`**: hypothesis plus `implicationIntroduction`, then `#print axioms`.

No totality of `C`, `X`, `W` or `members` is needed beyond the existing all-`Program` totality inside `optionGraphCases` and `programCompositionCases`. No standard-model step occurs anywhere.

**Missing helpers**
- **`memberSubst`**: exists twice but both copies are `private` (`RawMinimumOccurrenceOpenSyntaxProof.memberSubst`, `ScratchMembershipOpenSyntaxProof.graphSubst`). I will re-prove it locally (about 8 lines) rather than touch those files.
- **`tapeSubst`**: no public arity-3 version exists; new, local.
- **Nothing else.** No premise is strengthened.

## 4. Import closure estimate

I cannot count modules without the build tooling. There are five new small modules. Every dependency is already in the #732 / RawMinimumOccurrence / RawTickShape closures, plus the definition-only closure of `PackedLeastDefinitions`; no numeric-proof modules.

The one comparatively heavy import is `InternalComputabilityApplicationSyntaxProof`, needed for `existsEmbeddedSubst`. If Astra wants it out, I can re-derive that lemma locally from `InternalFiniteBlocksSubstitutionProof.existsSubst` and `onTermRelabel` (about 6 lines).

## 5. Unresolved issues

1. **Optional fourth conjunct.** The proof passes through `unary scratchMinimum (suc selected) pool` at the same pool. Retaining it in the row (as `parsedOccurrenceRow` does) costs nothing and would help a later least-semantics consumer. I kept the row to the three required conjuncts; root should decide before freeze.
2. **Tape normal forms.** `![…]` versus `Fin.cons … Fin.elim0` after `programRename`, and `ys` versus `![ys 0]`, are the main proof-engineering risk. Precedents handle both, but only compilation confirms it.
3. **Elaboration of `lift`.** The `let`-bound function in `poolOccurrence` should unfold by `rfl` as in `parsedOccurrence`. If it does not, I would inline the four double relabels; the statement is unchanged.
4. **Not asserted.** The target does not give `parserGraph (suc contextPayload) ctx`. That is one composition/projection step from the first conjunct and is left to a follow-on.

## Scope and ownership

This lane owns only new `NumberedWindowInternalSparsePackedLeastOpen{Definitions,Targets,SyntaxProof,BranchesProof,Checks}.lean`. It modifies no existing file and makes no numbered-theorem, calibration, parser-inversion, round-ancestry or least-semantics claim. Astra keeps the native queue, numerical C/X/W selection and tuple reinstallation; Sol keeps Paper17; the reviewer prescopes this target before I write any proof. After this leaf, the filter-membership inclusion gets coordinated with Astra.
