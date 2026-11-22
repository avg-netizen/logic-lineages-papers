module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename specialize)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph poolOccurrence)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (binder occurrenceUnfold)
open NumberedWindowInternalSparsePackedLeastOpenChecks (exact_OpenPackedLeastPoolOccurrence)
open NumberedWindowInternalSparseRoundWindowTargets

theorem exact_RoundsWindowFromRetained : ExactRoundsWindowFromRetained :=
  NumberedWindowInternalSparseRoundWindowInductionProof.roundsWindow

theorem exact_ChosenMembersWindowFromRetained : ExactChosenMembersWindowFromRetained :=
  NumberedWindowInternalSparseRoundWindowMembersProof.chosenWindow

private theorem atOccurrence (paid : ExactRetainedPredecessor) (C : Program 3) (X : Program 2)
    (W : Program 3) (s : Settings) {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (ctx ty seed k : OTerm α) (guard : Nonempty (Derivation body Γ (windowAt W ctx ty seed)))
    (occ : Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed k))) :
    Nonempty (Derivation body Γ (windowAt W ctx ty k)) := by
  rw [occurrenceUnfold] at occ
  let a := binder C X W s ctx ty seed k
  let Δ := existsOne a :: Γ.map weaken
  let Θ := a :: Δ.map weaken
  let lift (x : OTerm α) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) :=
    (x.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl
  let pool : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  have first := renameInto guard (Sum.inl : α → α ⊕ Fin 1) Δ
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  have second := renameInto first (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1) Θ
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [windowRename,windowRename] at second
  obtain ⟨g⟩ := second
  have atPool : Derivation body Θ a := Derivation.hypothesis List.mem_cons_self
  have row := Derivation.conjunctionRight atPool
  obtain ⟨chosen⟩ := exact_ChosenMembersWindowFromRetained paid C X W s body _ Θ
    (lift ctx) (lift ty) (lift seed) pool
  have every := Derivation.implicationElimination chosen
    (Derivation.conjunctionIntroduction g (Derivation.conjunctionLeft row))
  obtain ⟨atK⟩ := specialize W (lift ctx) (lift ty) pool (lift k) every
  have endResult : Derivation body Θ (weaken (weaken (windowAt W ctx ty k))) := by
    change Derivation body Θ (((windowAt W ctx ty k).relabel
      (Sum.inl : α → α ⊕ Fin 1)).relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1))
    rw [windowRename,windowRename]
    exact Derivation.implicationElimination atK (Derivation.conjunctionRight row)
  have withPayload : Derivation body Δ (weaken (windowAt W ctx ty k)) :=
    Derivation.existentialElimination (Derivation.hypothesis List.mem_cons_self) endResult
  obtain ⟨both⟩ := occ
  exact ⟨Derivation.existentialElimination both withPayload⟩

theorem exact_SelectedWindowFromRetained : ExactSelectedWindowFromRetained := by
  intro paid C X W s body α Γ ctx ty seed k
  let A := windowAt W ctx ty seed ⊓ leastGraph C X W s ctx ty seed k
  have h : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨pool⟩ := exact_OpenPackedLeastPoolOccurrence body α (A :: Γ) C X W s ctx ty seed k
  obtain ⟨result⟩ := atOccurrence paid C X W s ctx ty seed k ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.implicationElimination pool (Derivation.conjunctionRight h)⟩
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_RoundsWindowFromRetained
#print axioms exact_ChosenMembersWindowFromRetained
#print axioms exact_SelectedWindowFromRetained
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowChecks
