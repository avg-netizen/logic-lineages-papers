module
public import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighTargets
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighPointProof
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionChosenProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalRankedLiteralClauseHigh
open ActualSelectedSignedRouteProjection (exactChosenRouteProjection)

theorem exactRankedLiteralHighProjection : ExactRankedLiteralHighProjection := by
  intro f B selected r top baseline family setup prior minimum stable
  constructor
  · rintro ⟨outside,q,used,projected⟩
    obtain ⟨z,paid,holds⟩ :=
      (exactChosenRouteProjection f baseline top minimum q (highPacketShape r top family q used)).2.2.2.mp projected
    exact ⟨z,paid,(stable z paid).mpr outside,
      (exactRankedLiteralHigh f B selected r top baseline family setup z paid).mpr ⟨q,used,holds⟩⟩
  · rintro ⟨z,paid,outside,source⟩
    obtain ⟨q,used,holds⟩ := (exactRankedLiteralHigh f B selected r top baseline family setup z paid).mp source
    exact ⟨(stable z paid).mp outside,q,used,
      (exactChosenRouteProjection f baseline top minimum q (highPacketShape r top family q used)).2.2.2.mpr
        ⟨z,paid,holds⟩⟩

end LogicLineages.PermittedControl.OriginalRankedLiteralClauseHigh
