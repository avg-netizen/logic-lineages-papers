module
public import LogicLineages.PermittedControl.ActualGreatestRouteResidualTargets
public import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets
public import LogicLineages.PermittedControl.ActualSignedRouteCartesianTargets
public import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionTargets

/-! Opus B survey probe (not a target, not for a record): does the code
generator accept the bodies of the two `noncomputable` residual functions
when the marker is dropped, and is the post-packet typed pipeline computable? -/

public section
namespace LogicLineages.PermittedControl.JoinRegressionLaneS4ComputabilityProbe
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRouteProjection (project)
open OriginalProjectedMatrixDecode (decode)
open ActualGreatestRouteResidual (Residual keep)
open ActualGuardedResidualBitFamily (reifyFamily)
open ActualBitFamilyRawLayout (RawFamily encodeFamily)
open ActualSignedRouteCartesian (choices tuplePacket)
open ActualSymbolicPredecessorProjection (prepend)

/-- Literal body of `ActualGreatestRouteResidual.decodeRoute`, unmarked. -/
def decodeRoute (minimum : Nat) (q : Packet) : Option Residual :=
  let output := project minimum q
  (decode output.1 output.2).map (fun rs => ⟨output.1,output.2,rs⟩)

/-- Literal body of `ActualGreatestRouteResidual.lowerFamily`, unmarked. -/
def lowerFamily (top minimum : Nat) (qs : List Packet) : List Residual :=
  (keep top qs).filterMap (decodeRoute minimum)

theorem decodeRoute_eq : decodeRoute = ActualGreatestRouteResidual.decodeRoute := rfl
theorem lowerFamily_eq : lowerFamily = ActualGreatestRouteResidual.lowerFamily := rfl

/-- Typed pipeline from per-clause alternative rows to one encoded child. -/
def childFromRows (C top : Nat) (clauses : List (List (List Packet))) : RawFamily :=
  encodeFamily (reifyFamily C top
    (lowerFamily top C ((clauses.flatMap (fun rows => (choices rows).map tuplePacket)).map (prepend top))))

end LogicLineages.PermittedControl.JoinRegressionLaneS4ComputabilityProbe
