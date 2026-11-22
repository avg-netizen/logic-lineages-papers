module
public import LogicLineages.PermittedControl.ActualEffectiveHighTailNormalizationTargets
public import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidTerminalSignNormalization
open MixedSameRankResidue ActualZeroClassReplacement ActualZeroClassOutputState
open ActualWeightedReadNormalization ActualMixedRowLeadingSum ActualReadChargeIteration
open ActualFiniteGlobalTail ActualEffectiveGlobalTail ActualEffectiveTerminalSignBound

/-- Strengthened nonzero terminal: the same actual maximum, equation
and error are retained, with the exact current sign cutoff paid. -/
def SignedNonzeroTerminal (f ρ : Nat → Nat) (zRank : Nat) (s : ReadState) (xs : List Read) : Prop :=
  ∃ (annotations : List Annotation) (C : Nat),
    ChosenClass f ρ zRank xs annotations C ∧
    let terms := xs.map Prod.fst
    let parts := rowParts f C terms (xs.map Prod.snd) annotations
    let R := stateValue s
    let E := s.constant + parts.2
    parts.1 ≠ 0 ∧ 2 * R = parts.1 * (C : Int) + 2 * E ∧
    E.natAbs ≤ slopeBound terms * Nat.log2 C + (s.constant.natAbs + offsetBound terms) ∧
    SelectedLeadingSignCutoff.cutoff (slopeBound terms) (s.constant.natAbs + offsetBound terms)
      ≤ ρ zRank ∧
    rowCutoffCode s.constant (terms.map encodeWeighted) ≤ ρ zRank ∧
    (0 < R ↔ 0 < parts.1) ∧ (R < 0 ↔ parts.1 < 0) ∧
    (0 ≤ R ↔ 0 < parts.1) ∧ R ≠ 0

def SignedTerminal (f ρ : Nat → Nat) (zRank : Nat) (s : ReadState) : Prop :=
  ∃ xs, normalizeReads f ρ s.reads = some xs ∧
    ((¬ ActiveAt zRank xs ∧ LinearTerminal f ρ zRank s.constant s.reads xs) ∨
      (ActiveAt zRank xs ∧ SignedNonzeroTerminal f ρ zRank s xs))

/-- One original actual high-tail run, with a separately explicitly
paid executable cutoff at the original greatest rank. -/
def ExactActualPaidTerminalSignNormalization : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r zRank : Nat) (initial : ReadState), liftedReads f ρ initial.reads →
    RankBound r zRank initial → LongState initial →
    (∀ t ∈ syntaxOf initial,
      inputTailCode B r ((syntaxOf initial).map encodeWeighted) ≤ ρ t.2.rank) →
    inputSignBoundCode r initial.constant ((syntaxOf initial).map encodeWeighted) ≤ ρ zRank →
    ∃ (n : Nat) (final : ReadState), Trace f B ρ r zRank n initial final ∧
      n ≤ stateCharge r initial ∧ SignedTerminal f ρ zRank final ∧
      liftedReads f ρ final.reads ∧ RankBound r zRank final ∧
      OriginalRanks initial.reads final.reads ∧ stateValue initial = stateValue final

end LogicLineages.PermittedControl.ActualPaidTerminalSignNormalization
