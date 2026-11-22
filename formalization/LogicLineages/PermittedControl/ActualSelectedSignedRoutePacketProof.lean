module
public import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketTargets
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketFoldProof
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSelectedSignedRoutePacket
open ActualBoundedSignedRoutes (PacketHolds RouteHolds routes)

theorem exactEmittedRouteFamily : ExactEmittedRouteFamily := by
  intro f baseline top z fuel test positive s
  have chosen (path) (used : path ∈ routes top test positive fuel s) :=
    let h := exactEmittedRouteShape top fuel test positive s path used
    exactSelectedRoutePacket f baseline top z test positive path h.1 h.2
  refine ⟨fun p h => (chosen p h).1,?_⟩
  constructor
  · rintro ⟨p,h,passes⟩
    exact ⟨p,h,(chosen p h).2.1.mp passes⟩
  · rintro ⟨p,h,passes⟩
    exact ⟨p,h,(chosen p h).2.1.mpr passes⟩

end LogicLineages.PermittedControl.ActualSelectedSignedRoutePacket
