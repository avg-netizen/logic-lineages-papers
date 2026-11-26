module
public import LogicLineages.PermittedControl.PreparedStripReconstructionTargets
import LogicLineages.PermittedControl.PreparedStripReconstructionHitProof
import LogicLineages.PermittedControl.FiniteStripRecoveryFoldProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedStripReconstruction
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection FiniteStripRecovery FiniteStripCollectorRecovery

theorem closedHitDecision : ClosedHitDecision := by
  intro f x a rs p reads hin hall hhit
  have hreb (ρ : Nat → Nat) (hρ : ρ x = a) :=
    hitReconstruction f x a rs p reads ρ (fun _ => 0) hin hhit hρ
      (fun r hr hneq => (hneq (hall r hr)).elim)
  have hs : (foldFormula reads p).variables = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    obtain ⟨r,hr,_,hneq⟩ := (hreb (fun _ => a) rfl).2.2.2 i hi
    exact hneq (hall r hr)
  have hc : ClosedLinear.constantMatrix (foldFormula reads p) = true :=
    (ClosedLinearStatementChecks.exact_constant_matrix_test (foldFormula reads p)).mpr hs
  have hcCode : ClosedLinear.Code.constantMatrix (foldFormula reads p).encode = true :=
    (ClosedLinearStatementChecks.literal_code_calibration.1 (foldFormula reads p)).trans hc
  have hsCode : specializeCode f (x,a,rs.map encodeRequest,p.encode) =
      some (some (foldFormula reads p).encode) := by
    change (collectCode f x a (rs.map encodeRequest)).map
      (fun r => r.map (fun vals => foldCode vals p.encode)) = _
    rw [hhit]
    exact congrArg (fun c => some (some c)) (foldCodeExact.2 reads p)
  refine ⟨ClosedLinear.evaluateConstants (foldFormula reads p),?_,?_,?_⟩
  · rw [checkStripCode,hsCode]
    change some (some (constantCheck (foldFormula reads p).encode)) = _
    rw [constantCheck,hcCode,if_pos rfl,ClosedLinearStatementChecks.literal_code_calibration.2.1]
  · exact ((hreb (fun _ => a) rfl).2.1).symm.trans
      (ClosedLinearStatementChecks.actual_constant_evaluator (foldFormula reads p) hc (fun _ => 0)).symm
  · intro ρ hρ
    exact (hreb ρ hρ).1

end LogicLineages.PermittedControl.PreparedStripReconstruction
