module
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

theorem preparedProjectionCodeExact : PreparedProjectionCodeExact := by
  have hprim : Primrec (fun p : PreparedPacketCode => LinearRows.Code.eliminate 0 p.2) :=
    LinearRowsCodeStatementChecks.actual_numeric_programs.2.2.2.comp (Primrec.const 0) Primrec.snd
  have hcal (bytes : Nat) (p : NormalForm.Formula) :
      eliminatePreparedCode (bytes,p.encode) = (bytes,(eliminatePreparedFormula p).encode) :=
    congrArg (Prod.mk bytes) (LinearRowsCodeStatementChecks.literal_code_calibration.2.2.2 0 p)
  exact ⟨Primrec.fst.pair hprim,fun _ => rfl,hcal,fun table p => hcal (preparedTableBytes table) p⟩

end LogicLineages.PermittedControl.PreparedProjection
