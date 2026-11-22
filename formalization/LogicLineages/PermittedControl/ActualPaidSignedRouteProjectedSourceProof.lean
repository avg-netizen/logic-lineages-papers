module
public import LogicLineages.PermittedControl.ActualPaidSignedRouteProjectedSourceTargets
import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayProof
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidSignedRouteProjectedSource
open ActualPaidSignedRouteReplay (replayMinimum exactOriginalSignedRoutesAcrossReplay)
open ActualSelectedSignedRouteProjection (exactSignedRouteUnionProjection)
open ActualSyntaxChargeBudget (syntaxBudget)

theorem exactActualPaidSignedRouteProjectedSource : ExactActualPaidSignedRouteProjectedSource := by
  intro f B selected r top baseline s setup test positive prior minimum stable
  have first := exactSignedRouteUnionProjection f baseline top minimum (syntaxBudget r s.terms)
    test positive s prior stable
  refine first.trans ?_
  constructor
  · rintro ⟨z,paid,outside,route⟩
    exact ⟨z,paid,outside,
      (exactOriginalSignedRoutesAcrossReplay f B selected r top baseline s setup z paid test positive).mpr route⟩
  · rintro ⟨z,paid,outside,original⟩
    exact ⟨z,paid,outside,
      (exactOriginalSignedRoutesAcrossReplay f B selected r top baseline s setup z paid test positive).mp original⟩

end LogicLineages.PermittedControl.ActualPaidSignedRouteProjectedSource
