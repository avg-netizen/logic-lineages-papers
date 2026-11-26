module
public import LogicLineages.PermittedControl.ActualPaidSignedMatrixProjectionTargets
import LogicLineages.PermittedControl.ActualPaidSignedMatrixProjectionReplayProof
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionChosenProof
import LogicLineages.PermittedControl.ActualSignedRouteCartesianProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidSignedMatrixProjection
open ActualSignedRouteCartesian (tuplePacket exactActualSignedMatrixTuples)
open ActualSelectedSignedRouteProjection (exactChosenRouteProjection)

theorem exactPaidSignedMatrixProjection : ExactPaidSignedMatrixProjection := by
  intro f B selected r top baseline rows setup prior minimum stable
  have shape := (exactActualSignedMatrixTuples f baseline r top 0 rows).1
  constructor
  · rintro ⟨outside,positions,member,solved⟩
    obtain ⟨z,paid,holds⟩ :=
      (exactChosenRouteProjection f baseline top minimum (tuplePacket positions) (shape positions member)).2.2.2.mp solved
    have source := (exactActualSameHighMatrixTuples f B selected r top baseline rows setup z paid).mpr
      ⟨positions,member,holds⟩
    exact ⟨z,paid,(stable z paid).mpr outside,source⟩
  · rintro ⟨z,paid,outside,allRows⟩
    obtain ⟨positions,member,holds⟩ :=
      (exactActualSameHighMatrixTuples f B selected r top baseline rows setup z paid).mp allRows
    have solved :=
      (exactChosenRouteProjection f baseline top minimum (tuplePacket positions) (shape positions member)).2.2.2.mpr
        ⟨z,paid,holds⟩
    exact ⟨(stable z paid).mp outside,positions,member,solved⟩

end LogicLineages.PermittedControl.ActualPaidSignedMatrixProjection
