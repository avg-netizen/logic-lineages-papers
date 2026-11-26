module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureChildCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (measureRename pairRename)
open NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof (codePairCases)
open NumberedWindowInternalChosenAuxMeasureParentTargets

attribute [local irreducible] programGraph

theorem exact_OpenChosenAuxMeasureChildCases : ExactOpenChosenAuxMeasureChildCases := by
  intro M body α Γ q goal next
  let P := selectedMeasure (measureUpdate M chosenCombine)
  apply programCases P ![q] goal
  intro β j Δ m keep rawObserved
  rw [inputsRename] at rawObserved
  have observed : Nonempty (Derivation body Δ (measureGraph M chosenCombine m (q.relabel j))) :=
    rawObserved
  apply codePairCases m (goal.relabel j)
  intro γ k Ξ d b retain pair
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  have moved := renameInto observed k Ξ retain
  rw [measureRename] at moved
  simp only [Term.relabel_relabel] at moved
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ (m.relabel k) d b both ⟨moved,pair⟩

#print axioms exact_OpenChosenAuxMeasureChildCases

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureChildCasesProof
