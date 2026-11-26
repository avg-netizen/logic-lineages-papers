module
public import LogicLineages.PermittedControl.ActualHighTailNormalizationTargets
public import LogicLineages.PermittedControl.ActualEffectiveGlobalTailTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveHighTailNormalization
open MixedSameRankResidue ActualZeroClassReplacement ActualZeroClassOutputState
open ActualReadChargeIteration ActualFiniteGlobalTail ActualEffectiveGlobalTail

/-- The same fixed actual high-tail normalization, now funded by the
primitive-recursive sufficient source bound. The independent terminal
sign cutoff is still conditional. -/
def ExactActualEffectiveHighTailNormalization : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r zRank : Nat) (initial : ReadState), liftedReads f ρ initial.reads →
    RankBound r zRank initial → LongState initial →
    (∀ t ∈ syntaxOf initial,
      inputTailCode B r ((syntaxOf initial).map encodeWeighted) ≤ ρ t.2.rank) →
    ∃ (n : Nat) (final : ReadState), Trace f B ρ r zRank n initial final ∧
      n ≤ stateCharge r initial ∧ Terminal f ρ zRank final ∧
      liftedReads f ρ final.reads ∧ RankBound r zRank final ∧
      OriginalRanks initial.reads final.reads ∧ stateValue initial = stateValue final

end LogicLineages.PermittedControl.ActualEffectiveHighTailNormalization
