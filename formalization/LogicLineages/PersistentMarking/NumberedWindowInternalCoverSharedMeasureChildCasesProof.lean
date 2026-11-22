module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildrenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename unaryRename)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof (codePairCases)
open NumberedWindowInternalCoverSharedMeasureChildrenTargets

attribute [local irreducible] programGraph

theorem moveMeasuredChild {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}
    (R : Program 4) (j : α → β) (Δ : List (Formula β)) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    {q m d b : OTerm α} (child : SelectedMeasureData R body Γ q m d b) :
    SelectedMeasureData R body Δ (q.relabel j) (m.relabel j) (d.relabel j) (b.relabel j) := by
  have reported := renameInto child.selected j Δ keep
  have pair := renameInto child.coordinates j Δ keep
  rw [unaryRename] at reported
  rw [pairRename] at pair
  exact ⟨reported,pair⟩

theorem exact_OpenCoverMemoMeasuredChildCases : ExactOpenCoverMemoMeasuredChildCases := by
  intro R body α Γ q goal next
  apply programCases (selectedMeasure R) ![q] goal
  intro β j Δ m keep observed
  rw [inputsRename] at observed
  have actual : Nonempty (Derivation body Δ (unary (selectedMeasure R) m (q.relabel j))) := observed
  apply codePairCases m (goal.relabel j)
  intro γ k Ξ d b retain pair
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  have moved := renameInto actual k Ξ retain
  rw [unaryRename] at moved
  simp only [Term.relabel_relabel] at moved
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ (m.relabel k) d b both ⟨moved,pair⟩

#print axioms exact_OpenCoverMemoMeasuredChildCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildCasesProof
