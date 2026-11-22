module
public import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsTargets
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsContextProof
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsLinearProof
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsNonlinearProof
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsSoundnessProof
import LogicLineages.PermittedControl.ActualBoundedSignedRoutesProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
open ActualBoundedSignedRoutes (Route routes RouteHolds signedRoute prefixGuard linearRoute
  exactTypedRouteLayout exactPathLocalAvailability)
open ActualFiniteSignedNodeBranch (StaticActive nodePacket)
open ActualReadChargeIteration (stateValue stateCharge Trace)
open ActualFiniteGlobalTail (syntaxOf)
open ActualSyntaxChargeBudget (syntaxBudget exactChargeBudget)

theorem exactBoundedSignedRouteCompleteness : ExactBoundedSignedRouteCompleteness := by
  intro f B baseline r top z initial ctx test positive fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro n s path enough valid
      by_cases active : StaticActive top (syntaxOf s)
      · have facts := exactReachedNonlinearRoute f B baseline r top z initial ctx n s path active
        obtain ⟨a,listed,passing⟩ := facts.1
        have result := facts.2 a listed passing
        rcases result with ⟨zero,out,edge,literal⟩ | ⟨nonzero,sign⟩
        · let k := fuel-1
          have decreases := edge.strict
          have depth : fuel = k+1 := by dsimp [k]; omega
          have smaller : k < fuel := by omega
          have paid : stateCharge r out ≤ k := by dsimp [k]; omega
          have childTruth : test.test.atPolarity positive (stateValue out) := by
            rwa [← edge.sameValue]
          obtain ⟨child,atChild,childPasses⟩ :=
            ih k smaller (n+1) out (snoc path edge) paid childTruth
          let route := prefixGuard (nodePacket (syntaxOf s) top a) child
          have chosen : route ∈ routes top test positive fuel (stateSyntax s) :=
            (exactTypedRouteLayout top fuel test positive (stateSyntax s) route).mpr
              (Or.inr ⟨active,a,listed,Or.inr ⟨zero,k,stateSyntax out,depth,literal,child,atChild,rfl⟩⟩)
          exact ⟨route,chosen,(exactPathLocalAvailability f baseline top z test positive
            (nodePacket (syntaxOf s) top a) child).mpr ⟨passing,childPasses⟩⟩
        · let route := signedRoute top (stateSyntax s) a
          have chosen : route ∈ routes top test positive fuel (stateSyntax s) :=
            (exactTypedRouteLayout top fuel test positive (stateSyntax s) route).mpr
              (Or.inr ⟨active,a,listed,Or.inl ⟨nonzero,rfl⟩⟩)
          refine ⟨route,chosen,?_,(sign test positive).mp valid⟩
          intro p used
          have eq : p = nodePacket (syntaxOf s) top a := List.mem_singleton.mp used
          simpa only [eq] using passing
      · let route := linearRoute top test positive (stateSyntax s)
        have chosen : route ∈ routes top test positive fuel (stateSyntax s) :=
          (exactTypedRouteLayout top fuel test positive (stateSyntax s) route).mpr
            (Or.inl ⟨active,rfl⟩)
        exact ⟨route,chosen,(exactReachedLinearRoute f B baseline r top z initial ctx n s path
          active test positive).mpr valid⟩

theorem exactActualSufficientSignedRoutes : ExactActualSufficientSignedRoutes := by
  intro f B baseline r top z initial ctx test positive
  let fuel := syntaxBudget r (syntaxOf initial)
  let path : Trace f B (ActualRankedNormalizationSyntax.extend baseline top z) r top 0 initial initial :=
    .nil initial
  constructor
  · exact exactBoundedSignedRouteCompleteness f B baseline r top z initial ctx
      test positive fuel 0 initial path (exactChargeBudget.1 r initial)
  · rintro ⟨route,member,passes⟩
    exact exactBoundedSignedRouteSoundness f B baseline r top z initial ctx
      test positive fuel 0 initial path route member passes

end LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
