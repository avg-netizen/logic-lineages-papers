module
public import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionTargets
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionChosenProof
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSelectedSignedRouteProjection
open ActualBoundedSignedRoutes (routes)
open ActualSelectedSignedRoutePacket (packet exactEmittedRouteFamily)

theorem exactSignedRouteUnionProjection : ExactSignedRouteUnionProjection := by
  intro f baseline top minimum fuel test positive s prior stable
  have family (z : Nat) := exactEmittedRouteFamily f baseline top z fuel test positive s
  constructor
  · rintro ⟨outside,path,used,solved⟩
    have prepared := (family 0).1 path used
    obtain ⟨z,below,passes⟩ :=
      (exactChosenRouteProjection f baseline top minimum (packet test positive path) prepared).2.2.2.mp solved
    exact ⟨z,below,(stable z below).mpr outside,(family z).2.mp ⟨path,used,passes⟩⟩
  · rintro ⟨z,below,outside,path,used,passes⟩
    obtain ⟨selected,member,actual⟩ := (family z).2.mpr ⟨path,used,passes⟩
    have prepared := (family z).1 selected member
    exact ⟨(stable z below).mp outside,selected,member,
      (exactChosenRouteProjection f baseline top minimum (packet test positive selected) prepared).2.2.2.mpr
        ⟨z,below,actual⟩⟩

end LogicLineages.PermittedControl.ActualSelectedSignedRouteProjection
