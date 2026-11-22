module
public import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualInitialSignedCountCleanup
open OrdinalComparison PreparedProjection
open MixedSameRankResidue (properOperand)
open ActualSymbolicZeroSuccessor (SyntaxState cleanSyntax cleanupShift)
open ActualShortCountCleanup (LongCountOperand shortShift retained)
open ActualReadChargeIteration (ReadState stateValue)
open ActualBoundedSignedRouteSemantics (stateSyntax)
open ActualPaidSignedRouteReplay (SourceHolds)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualZeroClassReplacement (liftedReads)

def cleanup (s : SyntaxState) : SyntaxState :=
  ⟨s.constant + cleanupShift s.terms,cleanSyntax s.terms⟩

def cleanupRead (original : ReadState) : ReadState :=
  ⟨original.constant + shortShift original.reads,retained original.reads⟩

def ExactOriginalInitialCleanup : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (original : ReadState), liftedReads f ρ original.reads →
      let cleaned := cleanupRead original
      cleaned.reads.Sublist original.reads ∧
      stateSyntax cleaned = cleanup (stateSyntax original) ∧
      liftedReads f ρ cleaned.reads ∧
      (∀ t ∈ (stateSyntax cleaned).terms, t ∈ (stateSyntax original).terms ∧ LongCountOperand t.2) ∧
      stateValue cleaned = stateValue original

def ExactOriginalInitialCleanupTest : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (s : SyntaxState),
      (∃ original : ReadState, stateSyntax original = s ∧ liftedReads f ρ original.reads) →
      ∀ (test : OrderTest) (positive : Bool),
        (SourceHolds f ρ s test positive ↔ SourceHolds f ρ (cleanup s) test positive)

def FullActualInitialSignedCountCleanup : Prop :=
  ExactOriginalInitialCleanup ∧ ExactOriginalInitialCleanupTest

end LogicLineages.PermittedControl.ActualInitialSignedCountCleanup
