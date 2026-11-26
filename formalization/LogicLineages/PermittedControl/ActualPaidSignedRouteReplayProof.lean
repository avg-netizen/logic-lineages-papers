module
public import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayTargets
import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayContextProof
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsCompletenessProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidSignedRouteReplay
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualFiniteGlobalTail (syntaxOf)
open ActualBoundedSignedRouteSemantics (stateSyntax exactActualSufficientSignedRoutes)
open ActualReadChargeIteration (ReadState stateValue)
open ActualBoundedSignedRoutes (Route routes RouteHolds)
open ActualSyntaxChargeBudget (syntaxBudget)

theorem exactOriginalSignedRoutesAcrossReplay : ExactOriginalSignedRoutesAcrossReplay := by
  intro f B selected r top baseline s setup z minimum test positive
  obtain ⟨ex,ready⟩ := exactActualReplayContext f B selected r top baseline s setup z minimum
  have actual (original : ReadState) (frames : stateSyntax original = s)
      (live : ActualZeroClassReplacement.liftedReads f (Function.update baseline top z) original.reads) :
      (test.test.atPolarity positive (stateValue original) ↔
        ∃ path ∈ routes top test positive (syntaxBudget r s.terms) s,
          RouteHolds f baseline top z test positive path) := by
    have known := exactActualSufficientSignedRoutes f B baseline r top z original
      (ready original frames live) test positive
    have terms : syntaxOf original = s.terms := congrArg SyntaxState.terms frames
    rw [terms,frames] at known
    exact known
  constructor
  · rintro ⟨source,frames,live,sign⟩
    exact (actual source frames live).mp sign
  · intro someRoute
    obtain ⟨original,frames,live⟩ := ex
    exact ⟨original,frames,live,(actual original frames live).mpr someRoute⟩

end LogicLineages.PermittedControl.ActualPaidSignedRouteReplay
