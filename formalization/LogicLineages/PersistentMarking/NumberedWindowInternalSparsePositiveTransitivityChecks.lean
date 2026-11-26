module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityRulesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open NumberedWindowInternalSparseFieldInductionChecks (exact_SparseFieldInductionAtCode)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof (fromPositive)
open NumberedWindowInternalSparsePositiveTransitivityTargets
open NumberedWindowInternalSparsePositiveTransitivityBindingProof (instantiateAt)
open NumberedWindowInternalSparsePositiveTransitivityMotiveProof (motive motiveAt)
open NumberedWindowInternalSparsePositiveTransitivityRulesProof (motivePremises)

theorem exact_OpenFinishThenPositive : OpenFinishThenPositive := by
  intro body raw least α ctx ty first
  have founded := exact_SparseFieldInductionAtCode body α [] (motive raw least ctx ty) first
    (motivePremises body raw least ctx ty)
  rw [motiveAt] at founded
  exact founded

theorem exact_OpenPositiveTransitivity : OpenPositiveTransitivity := by
  intro body raw least α ctx ty source first mid second target
  let p := positiveAt raw least ctx ty source first mid ⊓ positiveAt raw least ctx ty mid second target
  have h : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨actualFinish⟩ := fromPositive raw least ctx ty source first mid ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨compose⟩ := instantiateAt (Γ := []) raw least ctx ty source first mid second target
    (exact_OpenFinishThenPositive body raw least α ctx ty first)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (weakenClosed compose [p])
    (Derivation.conjunctionIntroduction (Derivation.conjunctionRight actualFinish) (Derivation.conjunctionRight h)))⟩

#print axioms exact_OpenFinishThenPositive
#print axioms exact_OpenPositiveTransitivity
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityChecks
