module
public import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayTargets
public import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidSignedRouteProjectedSource
open OrdinalComparison
open ActualPaidSignedRouteReplay (SourceHolds LowerSetup replayMinimum)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualSelectedSignedRoutePacket (packet)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualBoundedSignedRoutes (routes)
open ActualSyntaxChargeBudget (syntaxBudget)

/-- Actual original one-row semantics on the right. On the left each
typed alternative has its own tied lower table; no read from any
other path is required. The exterior replay law is explicit. -/
def ExactActualPaidSignedRouteProjectedSource : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (s : SyntaxState), LowerSetup B r top baseline s →
    ∀ (test : OrderTest) (positive : Bool) (prior : (Nat → Nat) → Prop),
      let minimum := replayMinimum B r top baseline s
      (∀ z : Nat, minimum ≤ z → (prior (Function.update baseline top z) ↔ prior baseline)) →
      ((prior baseline ∧ ∃ path ∈ routes top test positive (syntaxBudget r s.terms) s,
          LowerHolds f baseline top (project minimum (packet test positive path))) ↔
        ∃ z : Nat, minimum ≤ z ∧ prior (Function.update baseline top z) ∧
          SourceHolds f (Function.update baseline top z) s test positive)

end LogicLineages.PermittedControl.ActualPaidSignedRouteProjectedSource
