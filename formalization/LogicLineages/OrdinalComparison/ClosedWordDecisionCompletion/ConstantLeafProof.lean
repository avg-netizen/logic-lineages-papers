module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineTargets
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.SupportProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.CodeCalibrationProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.CodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearStatementChecks

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.ConstantLeafProof
open WordLinearDecisionCompletion
open LayeredComparison.SnyatkovCompletion

/-- Empty raw support means literally no word occurrence, even of weight zero. -/
theorem empty_names_variables (p : Formula) (h : names p = []) : p.variables = [] := by
  exact (List.dedup_eq_nil p.variables).mp h

theorem empty_names_tokens (p : Formula) (h : names p = []) : p.tokens = [] := by
  have hv := empty_names_variables p h
  exact List.eq_nil_of_map_eq_nil hv

theorem constant_eval_at (p : Formula) (h : names p = []) (ν : Nat → Nat) :
    Machine.constant (Formula.encode p) = true ↔ Formula.eval ν p := by
  have ht := empty_names_tokens p h
  have hv : (liftFormula 0 p).variables = [] := by
    rw [WordLinearDecisionCompletion.Proof.lift_variables,ht,List.map_nil]
  have hc : ClosedLinear.constantMatrix (liftFormula 0 p) = true :=
    (ClosedLinearProof.exactConstantMatrixTest _).mpr hv
  unfold Machine.constant
  rw [WordLinearDecisionCompletion.Proof.lift_formula_code,
    ClosedLinearProof.evaluateConstants_calibration]
  exact (ClosedLinearProof.actualConstantEvaluator _ hc (parameterValuation 0 ν)).trans
    (WordLinearDecisionCompletion.Proof.lift_formula_eval 0 p ν)

theorem exactConstantEvaluation : MachineTargets.ExactConstantEvaluation := by
  intro floor p hp
  constructor
  · intro hc
    refine ⟨fun _ => 0,?_,?_,(constant_eval_at p hp (fun _ => 0)).mp hc⟩
    · intro i hi
      rw [empty_names_variables p hp] at hi
      contradiction
    · intro t ht
      rw [empty_names_tokens p hp] at ht
      contradiction
  · rintro ⟨ν,hfloor,hdomains,htrue⟩
    exact (constant_eval_at p hp ν).mpr htrue

attribute [local irreducible] Nat.sqrt Nat.unpair

theorem constant_primitive : Primrec Machine.constant := by
  exact ClosedLinearProof.actualNumericPrograms.2.1.comp
    (WordLinearDecisionCompletion.Proof.liftFormula_primitive.comp (Primrec.const 0) Primrec.id)

#print axioms empty_names_variables
#print axioms empty_names_tokens
#print axioms constant_eval_at
#print axioms exactConstantEvaluation
#print axioms constant_primitive

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.ConstantLeafProof
