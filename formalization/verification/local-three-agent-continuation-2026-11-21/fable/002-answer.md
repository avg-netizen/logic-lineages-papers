Nothing below has been compiled; I had read-only tools, so Astra's queue is the first check. The proof is the planned one: branch split on the actual `contextOption` output, zero branch refuted, composition inversion to expose the pool, then #732.

`NumberedWindowInternalSparsePackedLeastOpenSyntaxProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding bindTerm liftBind varBind sucRelabel sucSubst zSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (liftTerms liftTermSubst existsEmbeddedSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen

attribute [local irreducible] programGraph

/-- The literal matrix under both object quantifiers of `poolOccurrence`:
context payload is the outer bound variable, pool the inner one. -/
abbrev binder {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α) : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
  poolOccurrenceRow C X W s
    ((ctx.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
    ((ty.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
    ((seed.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
    ((selected.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
    (.var (.inl (.inr 0))) (.var (.inr 0))

theorem occurrenceUnfold {α : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected : OTerm α) :
    poolOccurrence C X W s ctx ty seed selected =
      existsOne (existsOne (binder C X W s ctx ty seed selected)) := rfl

private theorem tapeSubst {α β : Type} (a b c : OTerm α) (ts : α → OTerm β) :
    (fun i => ((![a,b,c] : Fin 3 → OTerm α) i).subst ts) =
      ![a.subst ts,b.subst ts,c.subst ts] := by
  funext i
  refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y =>
    Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) y) x) i <;> rfl

private theorem memberSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) =
      memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

theorem leastRename {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected : OTerm α) (j : α → β) :
    (leastGraph C X W s ctx ty seed selected).relabel j =
      leastGraph C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
        (selected.relabel j) := by
  simp only [leastGraph,programRename,sucRelabel,tripleInputsRename]

private theorem rowRename {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected payload pool : OTerm α) (j : α → β) :
    (poolOccurrenceRow C X W s ctx ty seed selected payload pool).relabel j =
      poolOccurrenceRow C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
        (selected.relabel j) (payload.relabel j) (pool.relabel j) := by
  simp only [poolOccurrenceRow,conjunctionRename,programRename,sucRelabel,tripleInputsRename,
    graphRename]

private theorem rowSubst {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected payload pool : OTerm α) (ts : α → OTerm β) :
    (poolOccurrenceRow C X W s ctx ty seed selected payload pool).subst (fun a => emb (ts a)) =
      poolOccurrenceRow C X W s (ctx.subst ts) (ty.subst ts) (seed.subst ts)
        (selected.subst ts) (payload.subst ts) (pool.subst ts) := by
  simp only [poolOccurrenceRow,conjunctionSubst,programSubst,tapeSubst,sucSubst,memberSubst]

/-- Renaming the free names commutes with both binders; the two bound
variables are fixed and the lifted free terms cannot be captured. -/
theorem occurrenceRename {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected : OTerm α) (j : α → β) :
    (poolOccurrence C X W s ctx ty seed selected).relabel j =
      poolOccurrence C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
        (selected.relabel j) := by
  rw [occurrenceUnfold,occurrenceUnfold,existsRename,existsRename]
  unfold binder
  rw [rowRename]
  simp only [Term.relabel_relabel] <;> rfl

/-- Introduce both literal quantifiers at explicit object witnesses:
first the context payload, then the pool, from the actual row. -/
theorem occurrenceIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected payload pool : OTerm α)
    (row : Nonempty (Derivation body Γ
      (poolOccurrenceRow C X W s ctx ty seed selected payload pool))) :
    Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed selected)) := by
  let c' : OTerm (α ⊕ Fin 1) := ctx.relabel Sum.inl
  let t' : OTerm (α ⊕ Fin 1) := ty.relabel Sum.inl
  let q' : OTerm (α ⊕ Fin 1) := seed.relabel Sum.inl
  let k' : OTerm (α ⊕ Fin 1) := selected.relabel Sum.inl
  let p' : OTerm (α ⊕ Fin 1) := payload.relabel Sum.inl
  let A : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
    poolOccurrenceRow C X W s (c'.relabel Sum.inl) (t'.relabel Sum.inl) (q'.relabel Sum.inl)
      (k'.relabel Sum.inl) (.var (.inl (.inr 0))) (.var (.inr 0))
  let B : Formula (α ⊕ Fin 1) :=
    poolOccurrenceRow C X W s c' t' q' k' p' (.var (.inr 0))
  have firstSlot :
      (Term.var (.inl (.inr 0)) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)).subst
        (liftTerms (bindTerm payload)) = p' := rfl
  have lastSlot :
      (Term.var (.inr 0) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)).subst
        (liftTerms (bindTerm payload)) =
        (Term.var (.inr 0) : OTerm (α ⊕ Fin 1)) := rfl
  have ho : instantiate (existsOne A) (emb payload) = existsOne B := by
    simp only [instantiate,bindEmbedding,existsEmbeddedSubst,A,B,rowSubst,liftTermSubst,
      c',t',q',k',liftBind,firstSlot,lastSlot]
  have hi : instantiate B (emb pool) =
      poolOccurrenceRow C X W s ctx ty seed selected payload pool := by
    simp only [instantiate,bindEmbedding,B,c',t',q',k',p',rowSubst,liftBind,varBind]
  obtain ⟨d⟩ := row
  change Nonempty (Derivation body Γ (existsOne (existsOne A)))
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb payload)
  rw [ho]
  apply Derivation.existentialIntroduction (emb pool)
  rw [hi]
  exact d

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
```

`NumberedWindowInternalSparsePackedLeastOpenBranchesProof.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenBranchesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed minimumAtMembers)
open NumberedWindowInternalSparseScratchMembershipOpenChecks (exact_OpenScratchMinimumOccurs)
open NumberedWindowInternalSparsePackedLeastOpen
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (occurrenceRename occurrenceIntro)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual zero context branch is the actual constant-zero program.
Its output cannot equal the observed successor on the same tape. -/
theorem reject (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α)
    (missing : Nonempty (Derivation body Γ (programGraph contextOption z ![ctx,ty,seed])))
    (accepted : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed selected))) :
    Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed selected)) := by
  have lost := zeroBranchElim contextOption (constantZero 3) (minimumAtMembers C X W s)
    (suc selected) (![ctx,ty,seed] : Fin 3 → OTerm α) missing accepted
  obtain ⟨impossible⟩ := valueUnique (constantZero 3) (suc selected) z
    (![ctx,ty,seed] : Fin 3 → OTerm α) lost
    (zeroConstantValue (![ctx,ty,seed] : Fin 3 → OTerm α))
  exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩

/-- The observed successor context tag selects the actual minimum branch.
Inverting its literal composition exposes the members output on the same
tape as an object eigenvariable; the checked scratch law gives occurrence. -/
theorem present (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected payload : OTerm α)
    (known : Nonempty (Derivation body Γ
      (programGraph contextOption (suc payload) ![ctx,ty,seed])))
    (accepted : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed selected))) :
    Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed selected)) := by
  have selectedBranch := successorBranchElim contextOption (constantZero 3)
    (minimumAtMembers C X W s) (suc selected) payload
    (![ctx,ty,seed] : Fin 3 → OTerm α) known accepted
  apply programCompositionCases scratchMinimum (fun _ : Fin 1 => membersAtSeed C X W s)
    (suc selected) (![ctx,ty,seed] : Fin 3 → OTerm α)
    (poolOccurrence C X W s ctx ty seed selected) selectedBranch
  intro β j ys Δ keep minimum pooledAll
  rw [occurrenceRename]
  have tagged := renameInto known j Δ keep
  rw [programRename,tripleInputsRename,sucRelabel] at tagged
  have pooled := pooledAll 0
  rw [tripleInputsRename] at pooled
  rw [sucRelabel] at minimum
  have tuple : (![ys 0] : Fin 1 → OTerm β) = ys := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  have least : Nonempty (Derivation body Δ
      (programGraph scratchMinimum (suc (selected.relabel j))
        (![ys 0] : Fin 1 → OTerm β))) := by
    rw [tuple]
    exact minimum
  obtain ⟨ofMinimum⟩ := exact_OpenScratchMinimumOccurs body β Δ (ys 0) (selected.relabel j)
  obtain ⟨minimumAt⟩ := least
  obtain ⟨taggedAt⟩ := tagged
  obtain ⟨pooledAt⟩ := pooled
  exact occurrenceIntro C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
    (selected.relabel j) (payload.relabel j) (ys 0)
    ⟨Derivation.conjunctionIntroduction taggedAt
      (Derivation.conjunctionIntroduction pooledAt
        (Derivation.implicationElimination ofMinimum minimumAt))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenBranchesProof
```

`NumberedWindowInternalSparsePackedLeastOpenChecks.lean`

```lean
module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenBranchesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePackedLeast (contextOption)
open NumberedWindowInternalSparsePackedLeastOpen
open NumberedWindowInternalSparsePackedLeastOpenTargets
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename occurrenceRename)
open NumberedWindowInternalSparsePackedLeastOpenBranchesProof (reject present)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem recover (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α)
    (accepted : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed selected))) :
    Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed selected)) := by
  apply optionGraphCases contextOption (![ctx,ty,seed] : Fin 3 → OTerm α)
    (poolOccurrence C X W s ctx ty seed selected)
  · intro β j Δ keep missing
    rw [tripleInputsRename] at missing
    rw [occurrenceRename]
    have h := renameInto accepted j Δ keep
    rw [leastRename] at h
    exact reject C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
      (selected.relabel j) missing h
  · intro β j Δ payload keep known
    rw [tripleInputsRename] at known
    rw [occurrenceRename]
    have h := renameInto accepted j Δ keep
    rw [leastRename] at h
    exact present C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
      (selected.relabel j) payload known h

theorem exact_OpenPackedLeastPoolOccurrence : ExactOpenPackedLeastPoolOccurrence := by
  intro body α Γ C X W s ctx ty seed selected
  obtain ⟨d⟩ := recover (body := body)
    (Γ := leastGraph C X W s ctx ty seed selected :: Γ)
    C X W s ctx ty seed selected ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_OpenPackedLeastPoolOccurrence
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
```

## Source dependencies used

**Frozen statement** (unchanged): `leastGraph`, `poolOccurrenceRow`, `poolOccurrence`, `ExactOpenPackedLeastPoolOccurrence`.

**Programs unfolded by definitional equality only**
- `NumberedWindowInternalSparsePackedLeast`: `packedLeastProgram`, `minimumAtMembers`, `contextOption`, `membersAtSeed`.
- `ID1Completion.InternalAcceptance`: `constantZero` (`branch` is exposed only by unification).
- `NumberedWindowInternalSparseOrderedMinimum`: `scratchMinimum`.

**Derivation steps**
- Case split on the actual `contextOption` output: `NumberedWindowInternalFreshProbeProof.optionGraphCases`.
- Branch elimination: `InternalAcceptanceBranchProof.zeroBranchElim`, `successorBranchElim`.
- Zero branch contradiction: `InternalLessThanSupportProof.zeroConstantValue`, `InternalControlGraphSupportProof.valueUnique`, `InternalTagArithmeticSupportProof.sucNeZeroApply`, `Derivation.explosion`.
- Pool witness: `InternalAcceptanceSupportProof.programCompositionCases` on `minimumAtMembers`.
- Occurrence: `NumberedWindowInternalSparseScratchMembershipOpenChecks.exact_OpenScratchMinimumOccurs` (#732) with `Derivation.implicationElimination`.
- Context transport: `InternalGraphCompositionFunctionalityProof.renameInto`.
- Closing: `Derivation.conjunctionIntroduction`, two `Derivation.existentialIntroduction`, `Derivation.hypothesis`, `Derivation.implicationIntroduction`.

**Syntax lemmas**
- Renaming: `programRename`, `tripleInputsRename`, `graphRename` (ScratchMembership), `conjunctionRename`, `existsRename`, `sucRelabel`, Mathlib `Term.relabel_relabel`.
- Substitution: `programSubst` (the `InternalRawListRecursionSyntaxProof` one), `conjunctionSubst`, `existsEmbeddedSubst`, `liftTerms`, `liftTermSubst`, `bindEmbedding`, `bindTerm`, `liftBind`, `varBind`, `sucSubst`, `zSubst`.
- Local re-proofs: `tapeSubst`, and `memberSubst` because both existing copies are `private`.

## Deviations and likely first diagnostics

- **Deviations from the turn-1 plan.** The instance equations are inline `have ho`/`hi` inside `occurrenceIntro` (the `goodIntro` pattern) rather than separate lemmas, and B2 is inlined in `present`.
- **Closest templates.** `RawMinimumOccurrenceOpen*`, `RawTickShapeSyntaxProof.goodIntro`/`goodRename`, and `ApplicationOutputCoreReportSyntaxProof.bodyRename`/`bodySubst`.
- **Where a failure is most likely.**
  - The two closing `simp only` calls (`ho`, `hi`) in `occurrenceIntro`.
  - `rw [tuple]` in `present`, which turns `ys` into `![ys 0]`.
  - The final `rfl` in `occurrenceRename`.
