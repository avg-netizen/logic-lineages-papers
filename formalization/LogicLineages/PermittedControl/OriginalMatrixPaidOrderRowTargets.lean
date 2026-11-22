module
public import LogicLineages.PermittedControl.OriginalMatrixActualReadTapeTargets
public import LogicLineages.PermittedControl.ActualPaidTerminalSignNormalizationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixPaidOrderRow
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)
open PreparedProjection (LowerOperand)
open ActualZeroClassReplacement (Read liftedReads)
open ActualReadChargeIteration (ReadState stateValue RankBound Trace stateCharge)
open ActualShortCountCleanup (shortLength retained shortShift)
open ActualFiniteGlobalTail (syntaxOf LongState)
open ActualPaidTerminalSignNormalization (SignedTerminal)
open HeterogeneousSignedMatrixSlice (Row actualRows)
open SignedRowGuardedTest (Test)
open OriginalMatrixActualReadTape (readState)

def keptSyntax (terms : List WeightedOperand) : List WeightedOperand :=
  terms.filter (fun t => decide (shortLength t.2 = 0))

def shortSyntaxShift : List WeightedOperand → Int
  | [] => 0
  | t :: rest => t.1 * (shortLength t.2 : Int) + shortSyntaxShift rest

def stateAfterShort (source : ReadState) : ReadState :=
  ⟨source.constant + shortShift source.reads,retained source.reads⟩

def guardBound (B r : Nat) (row : Row) : Nat :=
  ActualEffectiveGlobalTail.inputTailCode B r ((keptSyntax row.2.2).map encodeWeighted)

def signBound (r : Nat) (row : Row) : Nat :=
  ActualEffectiveTerminalSignBound.inputSignBoundCode r (row.2.1 + shortSyntaxShift row.2.2)
    ((keptSyntax row.2.2).map encodeWeighted)

def IsOrder : Test → Prop
  | .equalZero | .nonnegative | .positive => True
  | .congruence _ => False

/-- Real successful original tape, then actual positive-short count cleanup
on that tape. Labels, weights and adjustment are determined by input syntax. -/
def ExactSourceShortPreparation : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (row : Row) (source : ReadState), readState f ρ row = some source →
    let clean := stateAfterShort source
    syntaxOf source = row.2.2 ∧ source.constant = row.2.1 ∧
      (clean.reads).Sublist source.reads ∧
      syntaxOf clean = keptSyntax row.2.2 ∧
      clean.constant = row.2.1 + shortSyntaxShift row.2.2 ∧
      liftedReads f ρ clean.reads ∧ LongState clean ∧ stateValue clean = stateValue source

/-- Specialize #958 to an actual guarded source order/equality row, at one
fixed increasing rank valuation. The original occurrence tape pays the
true read domains before cleanup (even for a false requested polarity). -/
def ExactPaidSourceOrderRow : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r zRank : Nat) (row : Row) (v : Int) (positive : Bool),
    IsOrder row.1 → actualRows f ρ [row] [(v,positive)] →
    (∀ t ∈ row.2.2, t.2.rank < r ∧ t.2.rank ≤ zRank) →
    (∀ t ∈ keptSyntax row.2.2, guardBound B r row ≤ ρ t.2.rank) →
    signBound r row ≤ ρ zRank →
    ∃ (source : ReadState) (n : Nat) (final : ReadState),
      readState f ρ row = some source ∧ stateValue source = v ∧
      Trace f B ρ r zRank n (stateAfterShort source) final ∧
      n ≤ stateCharge r (stateAfterShort source) ∧
      SignedTerminal f ρ zRank final ∧
      liftedReads f ρ final.reads ∧ RankBound r zRank final ∧
      (∀ rd ∈ final.reads, ∃ t ∈ row.2.2, rd.1.2.rank = t.2.rank) ∧
      stateValue final = v ∧ row.1.atPolarity positive (stateValue final)

def FullOriginalMatrixPaidOrderRow : Prop := ExactSourceShortPreparation ∧ ExactPaidSourceOrderRow

end LogicLineages.PermittedControl.OriginalMatrixPaidOrderRow
