module
public import LogicLineages.PermittedControl.ActualFiniteGlobalTailTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualHighTailNormalization
open ActualZeroClassReplacement ActualZeroClassOutputState
open ActualReadChargeIteration ActualFiniteGlobalTail

/-- The original fixed-actual-assignment normalization on one paid
syntax-bound high tail. Only the reached-node annotation/transfer
guards are supplied by that tail; a nonzero terminal keeps its own
explicit conditional sign cutoff and a linear terminal keeps its
actual correlated lower-operand table. -/
def ExactActualHighTailNormalization : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r zRank : Nat) (initial : ReadState), liftedReads f ρ initial.reads →
    RankBound r zRank initial → LongState initial →
    PaidGlobalTail B r ρ (syntaxOf initial) →
    ∃ (n : Nat) (final : ReadState), Trace f B ρ r zRank n initial final ∧
      n ≤ stateCharge r initial ∧ Terminal f ρ zRank final ∧
      liftedReads f ρ final.reads ∧ RankBound r zRank final ∧
      OriginalRanks initial.reads final.reads ∧ stateValue initial = stateValue final

end LogicLineages.PermittedControl.ActualHighTailNormalization
