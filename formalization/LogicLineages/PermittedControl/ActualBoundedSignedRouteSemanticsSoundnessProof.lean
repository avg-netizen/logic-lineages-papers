module
public import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsTargets
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsContextProof
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsLinearProof
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsNonlinearProof
import LogicLineages.PermittedControl.ActualBoundedSignedRoutesProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
open ActualBoundedSignedRoutes (PacketHolds RouteHolds signedRoute prefixGuard
  exactTypedRouteLayout exactPathLocalAvailability)
open ActualFiniteSignedNodeBranch (nodePacket nodeCoefficient)
open ActualReadChargeIteration (stateValue)
open ActualFiniteGlobalTail (syntaxOf)

theorem exactBoundedSignedRouteSoundness : ExactBoundedSignedRouteSoundness := by
  intro f B baseline r top z initial ctx test positive fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro n s path route member holds
      have layout := (exactTypedRouteLayout top fuel test positive (stateSyntax s) route).mp member
      rcases layout with ⟨inactive,rfl⟩ | ⟨active,a,ha,branches⟩
      · exact (exactReachedLinearRoute f B baseline r top z initial ctx n s path inactive test positive).mp holds
      · have facts := exactReachedNonlinearRoute f B baseline r top z initial ctx n s path active
        rcases branches with ⟨nonzero,rfl⟩ | ⟨zero,k,out,depth,success,child,inChild,rfl⟩
        · have packet : PacketHolds f baseline top z (nodePacket (syntaxOf s) top a) :=
            holds.1 _ List.mem_cons_self
          have actual := facts.2 a ha packet
          rcases actual with ⟨canceled,_⟩ | ⟨_,sign⟩
          · exact False.elim (nonzero canceled)
          · exact (sign test positive).mpr holds.2
        · have pair := (exactPathLocalAvailability f baseline top z test positive
            (nodePacket (syntaxOf s) top a) child).mp holds
          have actual := facts.2 a ha pair.1
          rcases actual with ⟨_,reached,edge,exactOut⟩ | ⟨nonzero,_⟩
          · have eq : out = stateSyntax reached := Option.some.inj (success.symm.trans exactOut)
            have childMember : child ∈ ActualBoundedSignedRoutes.routes top test positive k (stateSyntax reached) :=
              eq ▸ inChild
            have valid := ih k (by omega) (n+1) reached (snoc path edge) child childMember pair.2
            rw [edge.sameValue]
            exact valid
          · exact False.elim (nonzero zero)

end LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
