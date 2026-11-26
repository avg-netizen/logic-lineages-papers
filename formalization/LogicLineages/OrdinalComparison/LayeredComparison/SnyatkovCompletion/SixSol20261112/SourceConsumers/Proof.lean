module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceConsumers.Targets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceConsumersProof
open SourceConsumers NonlinearProjectionCompletion
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

/-- Concrete-program specification obtained from the checked supplier's literal
compiler, ground evaluator and complete original source semantics. The already
proved solver is instantiated here; no semantic or effectiveness input is added. -/
private theorem sourceAnswerCorrect (p : SourceFormula) (hp : p.variables = [])
    (ν : Nat → Nat) : SourceDecision.answer p.encode = true ↔ p.eval ν := by
  have hnone : ∀ i ∈ (OriginalSourceElimination.eliminate p).variables, False := by
    intro i hi
    have h := OriginalSourceEliminationProof.originalSourceNameSupport p i hi
    rw [hp] at h
    exact List.not_mem_nil h
  have hv := ExpandedBooleanGraphProof.matrix_eval_congr
    (OriginalSourceElimination.eliminate p) (fun _ => 0) ν
    (fun i hi => False.elim (hnone i hi))
  change SourceDecision.groundMatrix (SourceDecision.eliminate p.encode) = true ↔ p.eval ν
  rw [SourceDecisionProof.literalSourceCompiler p]
  exact (SourceDecisionProof.groundMatrixCalibration (OriginalSourceElimination.eliminate p)).trans
    (hv.trans (OriginalSourceEliminationProof.actualSourceElimination p ν))

/-- Exact original name membership, rather than an occurrence count or a new
support approximation, supplies the closed-sentence side condition. -/
private theorem closedNames (names emitted : List Nat)
    (hs : ∀ i, i ∈ emitted ↔ i ∈ names) (hn : names = []) : emitted = [] := by
  cases emitted with
  | nil => rfl
  | cons i rest =>
    have hi := (hs i).mp (List.mem_cons.mpr (Or.inl rfl))
    rw [hn] at hi
    exact False.elim (List.not_mem_nil hi)

private theorem common_code (p : CommonHeadFirstOrder.Formula) :
    commonAnswer p.encode = SourceDecision.answer (CommonHeadFirstOrder.translate p).encode := by
  unfold commonAnswer
  rw [CommonHeadFirstOrderStatementChecks.literal_code_calibration p]

private theorem balanced_code (p : BalancedFirstOrder.Formula) :
    balancedAnswer p.encode = SourceDecision.answer (BalancedFirstOrder.translate p).encode := by
  unfold balancedAnswer
  rw [BalancedFirstOrderStatementChecks.literal_code_calibration p]

theorem actualCommonDecision : SourceConsumersTargets.ActualCommonDecision := by
  refine ⟨?_, common_code, ?_⟩
  · change Computable (fun code : Nat =>
      SourceDecision.answer (CommonHeadFirstOrder.Code.translate code))
    exact SourceDecisionProof.answer_computable.comp
      CommonHeadFirstOrderStatementChecks.actual_numeric_program
  · intro p hc hp ν
    rw [common_code p]
    have hs := closedNames p.variables (CommonHeadFirstOrder.translate p).variables
      (CommonHeadFirstOrderStatementChecks.exact_free_variables p) hp
    exact (sourceAnswerCorrect (CommonHeadFirstOrder.translate p) hs ν).trans
      (CommonHeadFirstOrderStatementChecks.actual_source_translation p hc ν)

theorem actualBalancedDecision : SourceConsumersTargets.ActualBalancedDecision := by
  refine ⟨?_, balanced_code, ?_⟩
  · change Computable (fun code : Nat =>
      SourceDecision.answer (BalancedFirstOrder.Code.translate code))
    exact SourceDecisionProof.answer_computable.comp
      BalancedFirstOrderStatementChecks.actual_numeric_program
  · intro p hc hp ν
    rw [balanced_code p]
    have hs := closedNames p.variables (BalancedFirstOrder.translate p).variables
      (BalancedFirstOrderStatementChecks.exact_free_variables p) hp
    have hpositive : BalancedFirstOrder.positive ν p := by
      intro i hi
      rw [hp] at hi
      exact False.elim (List.not_mem_nil hi)
    exact (sourceAnswerCorrect (BalancedFirstOrder.translate p) hs ν).trans
      (BalancedFirstOrderStatementChecks.actual_source_translation p hc ν hpositive)

theorem fullCommonHeadLayers : SourceConsumersTargets.FullCommonHeadLayers :=
  ⟨CommonHeadExactVariablesStatementChecks.actual_source_clause,
    CommonHeadExactVariablesStatementChecks.literal_code_calibration,
    CommonHeadExactVariablesStatementChecks.actual_output_program,
    CommonHeadFirstOrderStatementChecks.actual_source_translation,
    CommonHeadFirstOrderStatementChecks.exact_free_variables,
    CommonHeadFirstOrderStatementChecks.exact_universal_domains,
    actualCommonDecision⟩

theorem fullBalancedComparison : SourceConsumersTargets.FullBalancedComparison :=
  ⟨BalancedExactVariables.StatementChecks.truth_and_exact_variables,
    BalancedExactVariables.StatementChecks.actual_sign_semantics,
    BalancedExactVariables.StatementChecks.exact_typed_code_calibration,
    BalancedExactVariables.StatementChecks.all_code_computation,
    BalancedFirstOrderStatementChecks.actual_source_translation,
    BalancedFirstOrderStatementChecks.exact_free_variables,
    BalancedFirstOrderStatementChecks.exact_universal_domain,
    actualBalancedDecision⟩

#print axioms sourceAnswerCorrect
#print axioms closedNames
#print axioms common_code
#print axioms balanced_code
#print axioms actualCommonDecision
#print axioms actualBalancedDecision
#print axioms fullCommonHeadLayers
#print axioms fullBalancedComparison
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceConsumersProof
