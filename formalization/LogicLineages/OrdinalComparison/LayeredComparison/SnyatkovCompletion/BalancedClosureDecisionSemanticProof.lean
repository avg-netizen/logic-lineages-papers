module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionSemanticInterface
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceDecisionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionProof
open BalancedSyntax BalancedEvaluation BalancedClosureDecision

theorem exactPositiveGuard : BalancedClosureDecisionTargets.ExactPositiveGuard := by
  intro names ν
  induction names with
  | nil => simp [positiveFormula, BaseFormula.Formula.eval]
  | cons i names ih =>
      change (0 < ν i ∧ (positiveFormula names).eval ν) ↔ ∀ j ∈ i :: names, 0 < ν j
      rw [ih]
      simp

theorem literalGuardCode : BalancedClosureDecisionTargets.LiteralGuardCode := by
  intro names
  induction names with
  | nil => rfl
  | cons i names ih =>
      change CommonHeadCode.conjunction [(3, 0, 4 * i + 1)] (positiveCode names) =
        (BaseFormula.Formula.conjunction (.less (.numeral 0) (.variable i)) (positiveFormula names)).encode
      rw [ih]
      rfl

theorem exactTypedCodeCalibration : BalancedClosureDecisionTargets.ExactTypedCodeCalibration := by
  intro Γ C E F desired
  dsimp only
  simp only [existsCode, forallCode, BalancedRawCompiler.recursiveCode,
    BalancedClosureDecisionSuppliers.typedCalibration Γ C E F desired,
    BalancedClosureDecisionSuppliers.originalSupport Γ C E F,
    literalGuardCode (BalancedExactVariables.sourceSupport Γ C E F)]
  exact ⟨rfl, rfl⟩

theorem actualGuardedSemantics : BalancedClosureDecisionTargets.ActualGuardedSemantics := by
  classical
  intro Γ C E F desired ν hC hE hF
  have hp : (positiveFormula (BalancedExactVariables.sourceSupport Γ C E F)).eval ν ↔
      ∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i := by
    rw [exactPositiveGuard]
    simp only [BalancedExactVariables.sourceSupport, List.mem_dedup]
  dsimp only [existsFormula, forallFormula, BaseFormula.Formula.eval]
  rw [hp]
  constructor
  · exact and_congr_right (fun hpositive => BalancedClosureDecisionSuppliers.actualSign Γ C E F desired ν hC hE hF hpositive)
  · constructor
    · rintro (hnot | hformula) hpositive
      · exact False.elim (hnot hpositive)
      · exact (BalancedClosureDecisionSuppliers.actualSign Γ C E F desired ν hC hE hF hpositive).mp hformula
    · intro h
      by_cases hpositive : ∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i
      · exact Or.inr ((BalancedClosureDecisionSuppliers.actualSign Γ C E F desired ν hC hE hF hpositive).mpr (h hpositive))
      · exact Or.inl hpositive

theorem actualSourceClosures : BalancedClosureDecisionTargets.ActualSourceClosures := by
  intro Γ C E F desired b hC hE hF
  have he := (BaseBooleanSourceProof.actualClosureDecisions (existsFormula Γ C E F desired) b).1
  have ha := (BaseBooleanSourceProof.actualClosureDecisions (forallFormula Γ C E F desired) b).2
  rw [exists_congr (fun ν => (actualGuardedSemantics Γ C E F desired ν hC hE hF).1)] at he
  rw [forall_congr' (fun ν => (actualGuardedSemantics Γ C E F desired ν hC hE hF).2)] at ha
  dsimp only
  rw [existsAnswer, forallAnswer, (exactTypedCodeCalibration Γ C E F desired).1,
    (exactTypedCodeCalibration Γ C E F desired).2]
  exact ⟨he, ha⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionProof
