module
public import LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReadsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidSignedRouteReplay
open OrdinalComparison PreparedProjection
open ActualFiniteGlobalTail (globalTail syntaxOf)
open ActualGlobalComparisonCeiling (comparisonCeiling)
open ActualReadChargeIteration (ReadState stateValue)
open ActualRankedNormalizationSyntax (LowerStrict)
open ActualShortCountCleanup (LongCountOperand)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualPaidOrderedSyntaxReads (readCeiling)
open ActualBoundedSignedRouteSemantics (RunContext stateSyntax)
open ActualTraceSignCutoff (terminalCutoffCeiling)
open ActualBoundedSignedRoutes (routes RouteHolds)
open ActualSyntaxChargeBudget (syntaxBudget)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualZeroClassReplacement (liftedReads)
open MixedSameRankResidue (properOperand)

def dummy (s : SyntaxState) : ReadState := ⟨s.constant,s.terms.map fun t => (t,0)⟩

noncomputable def commonMinimum (B r : Nat) (s : SyntaxState) : Nat :=
  max (readCeiling s.terms) (max (globalTail B r s.terms) (comparisonCeiling B r s.terms))

/-- Literal upper-rank lower bound. No phantom preceding rank at top=0.
Its sign cutoff uses only original coefficients/operands and constant. -/
noncomputable def replayMinimum (B r top : Nat) (baseline : Nat → Nat) (s : SyntaxState) : Nat :=
  max (commonMinimum B r s)
    (max (terminalCutoffCeiling r (dummy s))
      (if top = 0 then 0 else baseline (top-1) + 1))

structure LowerSetup (B r top : Nat) (baseline : Nat → Nat) (s : SyntaxState) : Prop where
  strict : LowerStrict baseline top
  scope : ∀ t ∈ s.terms, t.2.rank < r ∧ t.2.rank ≤ top
  proper : ∀ t ∈ s.terms, properOperand t.2
  long : ∀ t ∈ s.terms, LongCountOperand t.2
  paid : ∀ t ∈ s.terms, t.2.rank < top → commonMinimum B r s ≤ baseline t.2.rank

def SourceHolds (f ρ : Nat → Nat) (s : SyntaxState) (test : OrderTest) (positive : Bool) : Prop :=
  ∃ original : ReadState, stateSyntax original = s ∧ liftedReads f ρ original.reads ∧
    test.test.atPolarity positive (stateValue original)

def ExactSignCutoffFromSyntax : Prop :=
  ∀ (r : Nat) (s : ReadState), terminalCutoffCeiling r s = terminalCutoffCeiling r (dummy (stateSyntax s))

def ExactActualReplayContext : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (s : SyntaxState), LowerSetup B r top baseline s →
    ∀ (z : Nat), replayMinimum B r top baseline s ≤ z →
      (∃ original : ReadState, stateSyntax original = s ∧
        liftedReads f (Function.update baseline top z) original.reads) ∧
      ∀ original : ReadState, stateSyntax original = s →
        liftedReads f (Function.update baseline top z) original.reads →
          RunContext f B baseline r top z original

def ExactOriginalSignedRoutesAcrossReplay : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (s : SyntaxState), LowerSetup B r top baseline s →
    ∀ (z : Nat), replayMinimum B r top baseline s ≤ z →
    ∀ (test : OrderTest) (positive : Bool),
      (SourceHolds f (Function.update baseline top z) s test positive ↔
        ∃ path ∈ routes top test positive (syntaxBudget r s.terms) s,
          RouteHolds f baseline top z test positive path)

def FullActualPaidSignedRouteReplay : Prop :=
  ExactSignCutoffFromSyntax ∧ ExactActualReplayContext ∧ ExactOriginalSignedRoutesAcrossReplay

end LogicLineages.PermittedControl.ActualPaidSignedRouteReplay
