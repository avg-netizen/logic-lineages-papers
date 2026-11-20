module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityRulesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySufficientProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalQuotientComparisonProof (equalToNext)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparseFieldInductionChecks (exact_SparseFieldInductionAtCode)
open NumberedWindowInternalSparsePositiveTerminalityTargets
open NumberedWindowInternalSparsePositiveTerminalityUniformBindingProof (atFuel)
open NumberedWindowInternalSparsePositiveTerminalityMotiveProof (motive motiveAt)
open NumberedWindowInternalSparsePositiveTerminalityRulesProof (motivePremises)

theorem sufficient : OpenSufficientFuelTerminal := by
  intro body raw least α ctx ty cert
  have h := exact_SparseFieldInductionAtCode body α [] (motive raw least ctx ty) cert
    (motivePremises body raw least ctx ty)
  rw [motiveAt] at h
  exact h

theorem chosen : OpenChosenFuelTerminal := by
  intro body raw least α out ctx ty current cert
  let known := loopGraph raw least out cert ctx ty current cert
  obtain ⟨d⟩ := atFuel (Γ := []) raw least ctx ty cert cert current out
    (sufficient body raw least α ctx ty cert)
  let d' := ID1Completion.InternalPositiveUnfoldingSupportProof.weakenClosed d [known]
  have b := equalToNext (body := body) (Gamma := [known]) (refl cert)
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination d' (Derivation.conjunctionIntroduction b
      (Derivation.hypothesis List.mem_cons_self)))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySufficientProof
