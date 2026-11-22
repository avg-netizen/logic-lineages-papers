module
public import LogicLineages.PermittedControl.ActualGreatestRouteResidualTargets
import LogicLineages.PermittedControl.ActualGreatestRouteResidualTableProof
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionChosenProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixDecodeProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosureSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGreatestRouteResidual
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualSelectedSignedRouteProjection (project exactChosenRouteProjection)
open ActualSelectedSignedRoutePacket (Shape)
open OriginalPrintedPlainMatrixProjectedSupport (argumentNames)
open OriginalProjectedMatrixDecode (decode exactProjectedMatrixDecode)
open OriginalProjectedMatrixSemantics (exactResidualMatrixInterface)
open OriginalPrintedPlainMatrixResidualClosure (residualArgumentNames)
open OriginalMatrixLinearLowerTable (assignment)

theorem exactDecodedActualResidual : ExactDecodedActualResidual := by
  intro f ρ top minimum q ready ranked
  let out := project minimum q
  have compiled := exactChosenRouteProjection f ρ top minimum q ready
  have lower : StrictLower top out.1 := compiled.1.symm ▸ ranked
  obtain ⟨rs,decoded⟩ := exactProjectedMatrixDecode.2.2 out.1 out.2 ⟨compiled.2.1,compiled.2.2.1⟩
  let concrete : Residual := ⟨out.1,out.2,rs⟩
  have body : decodeRoute minimum q = some concrete := by
    change (decode out.1 out.2).map _ = _
    rw [decoded] <;> rfl
  have names : OriginalMatrixLowDimension.supportSet (rows concrete) = argumentNames q.1 := by
    change OriginalMatrixLowDimension.supportSet (OriginalProjectedMatrixSemantics.availabilityRows out.1 ++ rs) = _
    rw [residualArgumentNames out.1 out.2 rs decoded,compiled.1]
  refine ⟨concrete,body,compiled.1,names,?_,?_⟩
  · intro i used
    rw [names] at used
    obtain ⟨op,member,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp used)
    exact ranked op member
  · have calibrated := exactLowerHoldsAtAssignment f ρ top out lower compiled.2.1 compiled.2.2.1
    have interface := exactResidualMatrixInterface f ρ top out.1 (assignment f ρ out.1) out.2 rs
      (assignmentFit f ρ top out.1 lower) compiled.2.1.1 decoded true
    exact calibrated.trans interface

end LogicLineages.PermittedControl.ActualGreatestRouteResidual
