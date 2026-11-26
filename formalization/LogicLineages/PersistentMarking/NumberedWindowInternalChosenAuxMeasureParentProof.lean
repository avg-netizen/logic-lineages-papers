module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureAlignProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (measureRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalChosenAuxMeasureChildCasesProof (exact_OpenChosenAuxMeasureChildCases)
open NumberedWindowInternalChosenAuxMeasureAlignProof (exact_OpenChosenAuxMeasureAlign moveChild)
open NumberedWindowInternalChosenAuxMeasureParentTargets

theorem exact_OpenChosenAuxMeasureParent : ExactOpenChosenAuxMeasureParent := by
  intro M body α Γ dom cod fn arg p goal parent next
  apply exact_OpenChosenAuxMeasureChildCases M body α Γ fn goal
  intro β j Δ mf df bf keep fnData
  apply exact_OpenChosenAuxMeasureChildCases M body β Δ (arg.relabel j) (goal.relabel j)
  intro γ k Ξ ma da ba retain argData
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  have fnData' := moveChild M k Ξ retain fnData
  simp only [Term.relabel_relabel] at fnData' argData
  have parent' := renameInto parent (k ∘ j) Ξ both
  rw [measureRename,auxiliaryRename] at parent'
  have aligned := exact_OpenChosenAuxMeasureAlign M body γ Ξ
    (dom.relabel (k ∘ j)) (cod.relabel (k ∘ j)) (fn.relabel (k ∘ j)) (arg.relabel (k ∘ j))
    (mf.relabel k) ma (p.relabel (k ∘ j)) (df.relabel k) da (bf.relabel k) ba parent' fnData' argData
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ (mf.relabel k) ma (df.relabel k) da (bf.relabel k) ba both fnData' argData aligned

#print axioms exact_OpenChosenAuxMeasureParent

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentProof
