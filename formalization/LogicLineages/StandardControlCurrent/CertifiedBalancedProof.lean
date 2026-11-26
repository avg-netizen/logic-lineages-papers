module
public import LogicLineages.StandardControlCurrent.CertifiedBalancedTargets
public import LogicLineages.StandardControlCurrent.SnyatkovDecisionStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderStatementChecks
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CertifiedBalancedProof
open OrdinalComparison LayeredComparison LayeredComparison.SnyatkovCompletion

theorem lowerCertificateClosure : CertifiedBalancedTargets.LowerCertificateClosure :=
  ⟨BalancedSyntax.Affine.StatementChecks.literal_affine_closure,
    BalancedSyntax.Affine.StatementChecks.exact_affine_support,
    BalancedSyntax.Affine.StatementChecks.actual_lower_and_inputs,
    BalancedSyntax.Affine.StatementChecks.actual_canceled_descent⟩

theorem exactPointwise : CertifiedBalancedTargets.ExactPointwise :=
  ⟨BalancedExactVariables.StatementChecks.truth_and_exact_variables,
    BalancedExactVariables.StatementChecks.actual_sign_semantics,
    BalancedExactVariables.StatementChecks.exact_typed_code_calibration,
    BalancedExactVariables.StatementChecks.all_code_computation⟩

theorem exactTranslation : CertifiedBalancedTargets.ExactTranslation :=
  ⟨BalancedFirstOrderStatementChecks.actual_source_translation,
    BalancedFirstOrderStatementChecks.exact_free_variables,
    BalancedFirstOrderStatementChecks.literal_code_calibration,
    BalancedFirstOrderStatementChecks.actual_numeric_program,
    BalancedFirstOrderStatementChecks.exact_universal_domain⟩

theorem actualClosedAnswer : CertifiedBalancedTargets.ActualClosedAnswer := by
  have ha := SnyatkovDecisionStatementChecks.actualClosedAnswer
  refine ⟨ha.1.comp BalancedFirstOrderStatementChecks.actual_numeric_program, ?_, ?_⟩
  · intro p
    rw [BalancedFirstOrderStatementChecks.literal_code_calibration p]
  · intro p hcert hp ν
    rw [BalancedFirstOrderStatementChecks.literal_code_calibration p]
    have hclosed : (BalancedFirstOrder.translate p).variables = [] := by
      cases h : (BalancedFirstOrder.translate p).variables with
      | nil => rfl
      | cons i rest =>
        have hi : i ∈ (BalancedFirstOrder.translate p).variables := by
          rw [h]
          exact List.mem_cons_self
        have ho := (BalancedFirstOrderStatementChecks.exact_free_variables p i).mp hi
        rw [hp] at ho
        exact False.elim (List.not_mem_nil ho)
    have hpositive : BalancedFirstOrder.positive ν p := by
      intro i hi
      rw [hp] at hi
      exact False.elim (List.not_mem_nil hi)
    exact (ha.2 (BalancedFirstOrder.translate p) hclosed ν).trans
      (BalancedFirstOrderStatementChecks.actual_source_translation p hcert ν hpositive)

theorem fullBalancedComparison : CertifiedBalancedTargets.FullBalancedComparison :=
  ⟨exactPointwise, exactTranslation, actualClosedAnswer⟩

end LogicLineages.StandardControlCurrent.CertifiedBalancedProof
