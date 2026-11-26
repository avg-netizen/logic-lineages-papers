module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedCallsBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedAdvanceCompositionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityChecks (exact_OpenPositiveTransitivity)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedCases suppliedRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalThinMatchedCallsTargets (pulled)
open NumberedWindowInternalThinMatchedCallsBindingProof (provideEarlier pulledRename)
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem pullCases (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    (ctx cod parent value : OTerm α) (goal : Formula α)
    (h : Nonempty (Derivation body Γ (pulled C X W s raw ctx cod parent value)))
    (finish : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (earlier : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Derivation body Δ (leastGraph C X W s (ctx.relabel j) (cod.relabel j) (parent.relabel j) earlier) →
      Derivation body Δ (supplied raw (packedLeastProgram C X W s) (ctx.relabel j) (cod.relabel j) earlier (value.relabel j)) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let clause := leastGraph C X W s (ctx.relabel j) (cod.relabel j) (parent.relabel j) x ⊓
    supplied raw (packedLeastProgram C X W s) (ctx.relabel j) (cod.relabel j) x (value.relabel j)
  let Δ := clause :: Γ.map weaken
  have both : Derivation body Δ clause := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := finish _ j Δ x (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    (Derivation.conjunctionLeft both) (Derivation.conjunctionRight both)
  obtain ⟨h⟩ := h
  exact ⟨Derivation.existentialElimination h d⟩

private theorem compose (raw : Program 5) (least : Program 3) (ctx cod a b c : OTerm α)
    (first : Nonempty (Derivation body Γ (supplied raw least ctx cod a b)))
    (last : Nonempty (Derivation body Γ (supplied raw least ctx cod b c))) :
    Nonempty (Derivation body Γ (supplied raw least ctx cod a c)) := by
  apply suppliedCases raw least ctx cod a b _ first
  intro β j Δ p keep x
  rw [suppliedRename]
  have latter := renameInto last j Δ keep
  rw [suppliedRename] at latter
  apply suppliedCases raw least _ _ _ _ _ latter
  intro γ k Θ q hold y
  rw [suppliedRename]
  have former := renameInto x k Θ hold
  rw [positiveRename] at former
  obtain ⟨former⟩ := former
  obtain ⟨y⟩ := y
  exact closedApply (exact_OpenPositiveTransitivity body raw least γ _ _ _ (p.relabel k) _ q _)
    ⟨Derivation.conjunctionIntroduction former y⟩

theorem continuePath (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    (ctx cod parent mid value : OTerm α)
    (first : Nonempty (Derivation body Γ (pulled C X W s raw ctx cod parent mid)))
    (last : Nonempty (Derivation body Γ (supplied raw (packedLeastProgram C X W s) ctx cod mid value))) :
    Nonempty (Derivation body Γ (pulled C X W s raw ctx cod parent value)) := by
  apply pullCases C X W s raw ctx cod parent mid _ first
  intro β j Δ earlier keep found path
  rw [pulledRename]
  have l := renameInto last j Δ keep
  rw [suppliedRename] at l
  obtain ⟨joined⟩ := compose raw (packedLeastProgram C X W s) _ _ earlier _ _ ⟨path⟩ l
  exact provideEarlier C X W s raw _ _ _ _ earlier found joined
#print axioms pullCases
#print axioms continuePath
end LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedAdvanceCompositionProof
