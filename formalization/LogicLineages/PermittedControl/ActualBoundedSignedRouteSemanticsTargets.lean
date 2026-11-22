module
public import LogicLineages.PermittedControl.ActualBoundedSignedRoutesTargets
public import LogicLineages.PermittedControl.ActualGlobalComparisonCeilingTargets
public import LogicLineages.PermittedControl.ActualTraceSignCutoffTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
open OrdinalComparison FieldComparison PreparedProjection
open ActualFullLabelPairGuards (Answer)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualRankedNormalizationSyntax (extend LowerStrict AboveLower)
open ActualFiniteGlobalTail (syntaxOf LongState PaidGlobalTail)
open ActualGlobalComparisonCeiling (PaidComparisonCeiling)
open ActualTraceSignCutoff (terminalCutoffCeiling)
open ActualZeroClassReplacement (liftedReads)
open ActualReadChargeIteration (ReadState RankBound Trace ZeroEdge stateCharge stateValue)
open ActualSymbolicZeroSuccessor (SyntaxState successor)
open ActualBoundedSignedRoutes (Route PacketHolds RouteHolds routes linearRoute)
open ActualFiniteSignedNodeBranch (StaticActive nodePattern nodePacket nodeCoefficient)
open ActualSyntaxChargeBudget (syntaxBudget)

def stateSyntax (s : ReadState) : SyntaxState := ⟨s.constant,syntaxOf s⟩

/-- Three independent paid quantities: true annotation/transfer tails,
the true finite comparison maximum, and the signed terminal cutoff.
These are numerical hypotheses at the original rank assignment, not
statements that arbitrary values pay all three. -/
structure RunContext (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat)
    (r top z : Nat) (initial : ReadState) : Prop where
  chosen : SelectedWithThreshold f B
  lower : LowerStrict baseline top
  above : AboveLower baseline top z
  live : liftedReads f (Function.update baseline top z) initial.reads
  ranks : RankBound r top initial
  long : LongState initial
  transferTail : PaidGlobalTail B r (Function.update baseline top z) (syntaxOf initial)
  comparisonTail : PaidComparisonCeiling B r (Function.update baseline top z) (syntaxOf initial)
  signTail : terminalCutoffCeiling r initial ≤ z

def RealBranch (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat)
    (r top z : Nat) (s : ReadState) (a : List Answer) : Prop :=
  let raw := syntaxOf s
  let coef := nodeCoefficient raw a
  (coef = 0 ∧ ∃ out : ReadState,
      ZeroEdge f B (extend baseline top z) r top s out ∧
        successor s.constant raw a = some (stateSyntax out)) ∨
  (coef ≠ 0 ∧ ∀ (test : OrderTest) (positive : Bool),
    ((test.test.atPolarity positive (stateValue s)) ↔ test.test.atPolarity positive coef))

def ExactReachedLinearRoute : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    RunContext f B baseline r top z initial →
    ∀ (n : Nat) (s : ReadState), Trace f B (extend baseline top z) r top n initial s →
    ¬ StaticActive top (syntaxOf s) →
    ∀ (test : OrderTest) (positive : Bool),
      (RouteHolds f baseline top z test positive (linearRoute top test positive (stateSyntax s)) ↔
        test.test.atPolarity positive (stateValue s))

def ExactReachedNonlinearRoute : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    RunContext f B baseline r top z initial →
    ∀ (n : Nat) (s : ReadState), Trace f B (extend baseline top z) r top n initial s →
    StaticActive top (syntaxOf s) →
      (∃ a ∈ nodePattern (syntaxOf s), PacketHolds f baseline top z (nodePacket (syntaxOf s) top a)) ∧
      ∀ a ∈ nodePattern (syntaxOf s), PacketHolds f baseline top z (nodePacket (syntaxOf s) top a) →
        RealBranch f B baseline r top z s a

def ExactBoundedSignedRouteSoundness : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    RunContext f B baseline r top z initial →
    ∀ (test : OrderTest) (positive : Bool) (fuel n : Nat) (s : ReadState),
      Trace f B (extend baseline top z) r top n initial s →
      ∀ route ∈ routes top test positive fuel (stateSyntax s),
        RouteHolds f baseline top z test positive route →
          test.test.atPolarity positive (stateValue s)

def ExactBoundedSignedRouteCompleteness : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    RunContext f B baseline r top z initial →
    ∀ (test : OrderTest) (positive : Bool) (fuel n : Nat) (s : ReadState),
      Trace f B (extend baseline top z) r top n initial s →
      stateCharge r s ≤ fuel →
      test.test.atPolarity positive (stateValue s) →
        ∃ route ∈ routes top test positive fuel (stateSyntax s),
          RouteHolds f baseline top z test positive route

def ExactActualSufficientSignedRoutes : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (baseline : Nat → Nat) (r top z : Nat) (initial : ReadState),
    RunContext f B baseline r top z initial →
    ∀ (test : OrderTest) (positive : Bool),
      (test.test.atPolarity positive (stateValue initial) ↔
        ∃ route ∈ routes top test positive (syntaxBudget r (syntaxOf initial)) (stateSyntax initial),
          RouteHolds f baseline top z test positive route)

def FullActualBoundedSignedRouteSemantics : Prop :=
  ExactReachedLinearRoute ∧ ExactReachedNonlinearRoute ∧
  ExactBoundedSignedRouteSoundness ∧ ExactBoundedSignedRouteCompleteness ∧ ExactActualSufficientSignedRoutes

end LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
