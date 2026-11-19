module
public import LogicLineages.StandardControlCurrent.CertifiedCommonTargets
public import LogicLineages.StandardControlCurrent.SnyatkovDecisionStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderStatementChecks
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CertifiedCommonProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion

theorem exactPointwise : CertifiedCommonTargets.ExactPointwise :=
  ⟨CommonHeadExactVariablesStatementChecks.actual_source_clause,
    CommonHeadExactVariablesStatementChecks.literal_code_calibration,
    CommonHeadExactVariablesStatementChecks.actual_output_program⟩

theorem exactTranslation : CertifiedCommonTargets.ExactTranslation :=
  ⟨CommonHeadFirstOrderStatementChecks.actual_source_translation,
    CommonHeadFirstOrderStatementChecks.exact_free_variables,
    CommonHeadFirstOrderStatementChecks.literal_code_calibration,
    CommonHeadFirstOrderStatementChecks.actual_numeric_program,
    CommonHeadFirstOrderStatementChecks.exact_universal_domains⟩

theorem actualClosedAnswer : CertifiedCommonTargets.ActualClosedAnswer := by
  have ha := SnyatkovDecisionStatementChecks.actualClosedAnswer
  refine ⟨ha.1.comp CommonHeadFirstOrderStatementChecks.actual_numeric_program, ?_, ?_⟩
  · intro p
    rw [CommonHeadFirstOrderStatementChecks.literal_code_calibration p]
  · intro p hcert hp ν
    rw [CommonHeadFirstOrderStatementChecks.literal_code_calibration p]
    have hclosed : (CommonHeadFirstOrder.translate p).variables = [] := by
      cases h : (CommonHeadFirstOrder.translate p).variables with
      | nil => rfl
      | cons i rest =>
        have hi : i ∈ (CommonHeadFirstOrder.translate p).variables := by
          rw [h]
          exact List.mem_cons_self
        have ho := (CommonHeadFirstOrderStatementChecks.exact_free_variables p i).mp hi
        rw [hp] at ho
        exact False.elim (List.not_mem_nil ho)
    exact (ha.2 (CommonHeadFirstOrder.translate p) hclosed ν).trans
      (CommonHeadFirstOrderStatementChecks.actual_source_translation p hcert ν)

theorem fullCommonHeadLayers : CertifiedCommonTargets.FullCommonHeadLayers :=
  ⟨exactPointwise, exactTranslation, actualClosedAnswer⟩

end LogicLineages.StandardControlCurrent.CertifiedCommonProof
