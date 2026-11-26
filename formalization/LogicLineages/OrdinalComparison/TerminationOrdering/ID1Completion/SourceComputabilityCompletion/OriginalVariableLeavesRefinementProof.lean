module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesNativeBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesRefinementProof
open OriginalVariableLeaves OriginalVariableLeavesEvaluationProof OriginalVariableLeavesNativeBranchProof
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalAcceptanceCalibrationProof UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalVariableLeavesRefinementEquality :
    OriginalVariableLeavesTargets.ActualOriginalVariableLeavesRefinementEquality := by
  intro n arity guard data hg hc v
  have hv : v = List.Vector.ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i <;> rfl
  rw [hv]
  change evaluate (source data.oldSource data.member) _ = _ ∧
    evaluate (target guard data.oldTarget) _ = _
  rw [source,target,evalBranch,evalBranch,variableTagEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero]
  by_cases htag : (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 0
  · simp only [htag,ite_true,show (1 : Nat) ≠ 0 from Nat.one_ne_zero,ite_false]
    exact variableBranchesEqual n arity guard data hg hc (v.get 0) (v.get 1) htag
  · simp only [htag,ite_false,ite_true,and_self]

theorem refinedCalibration (n : Nat) (arity : Fin n → Nat) (guard : Program 1)
    (data : Data) (hg : ContextGuardCalibrated n guard) (hc : Calibrated n arity data) :
    Calibrated n arity (refineData guard data) := by
  refine ⟨?_,?_,hc.2.2.1,hc.2.2.2⟩
  · intro v
    exact (actualOriginalVariableLeavesRefinementEquality n arity guard data hg hc v).1.trans (hc.1 v)
  · intro v
    exact (actualOriginalVariableLeavesRefinementEquality n arity guard data hg hc v).2.trans (hc.2.1 v)

theorem refinedInputsCalibration (n : Nat) (arity : Fin n → Nat) (guard : Program 1)
    (p : GlobalSourcePackage.Inputs) (hg : ContextGuardCalibrated n guard)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (refineInputs guard p) := by
  exact ⟨refinedCalibration n arity guard p.base hg hp.1,hp.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesRefinementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesRefinementProof
