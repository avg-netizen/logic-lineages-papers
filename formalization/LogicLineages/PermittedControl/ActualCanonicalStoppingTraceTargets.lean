module
public import LogicLineages.PermittedControl.ActualCanonicalNodeProgressTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalStoppingTrace
open OrdinalComparison PreparedProjection
open ActualReadChargeIteration (ReadState RankBound ActiveAt NodeGuards stateValue stateCharge)
open ActualCanonicalOperandGrouping ActualCanonicalZeroTrace
open ActualCanonicalNodeProgress (ProgressAt)
open ActualZeroClassReplacement ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open ActualFullValueLabels ActualFullLabelPairGuards ActualFiniteFullValueGuards ActualFullValueMaximalMetadata
open ActualFiniteGlobalTail ActualGlobalComparisonCeiling
open ActualZeroClassOutputState (OriginalRanks)
open ActualZeroClassCohortTransfer

/-- Actual nonzero candidate at the selected own-order maximum. This
retains source value identity but does not turn nonzero into a sign. -/
def NonzeroStop (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
    (s : ReadState) (xs : List Read) : Prop :=
  let terms := xs.map Prod.fst
  let vals := xs.map Prod.snd
  ∃ (a : List Answer) (anns : List Annotation) (C : Nat) (ν : Nat → Nat),
    a ∈ patterns (pairs (labels terms)).length ∧
    Matches f ρ (pairs (labels terms)) a ∧
    (let packet := compile top (pairs (labels terms)) a
     PreparedTableTied f top ρ packet.1 ν ∧ packet.2.eval (Function.update ν 0 (ρ top))) ∧
    AlignedAnnotations f ρ terms vals anns ∧
    (fullValues f anns).max? = some C ∧ f (ρ top) ≤ C ∧
    NodeGuards B ρ xs ∧ Ready f B ρ C terms anns ∧ TransferReady B ρ (cohort f C terms anns) ∧
    maximalCoefficient terms a = (rowParts f C terms vals anns).1 ∧
    maximalCoefficient terms a ≠ 0 ∧
    2 * stateValue s = maximalCoefficient terms a * (C : Int) +
      2 * (s.constant + (rowParts f C terms vals anns).2)

def StopsAt (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat) (s : ReadState) : Prop :=
  ∃ xs, normalizeCanonical f ρ s.reads = some xs ∧ liftedReads f ρ xs ∧
    (¬ ActiveAt top xs ∨ (ActiveAt top xs ∧ NonzeroStop f B ρ r top s xs))

/-- Keep exactly the ordered raw answer-vector codes of the actual trace. -/
def encodeAnswers (answers : List (List Answer)) : List (List Nat) :=
  answers.map (List.map Answer.code)

def ExactCanonicalProgressSplit : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat) (s : ReadState),
    ProgressAt f B ρ r top s →
    StopsAt f B ρ r top s ∨ ∃ (a : List Answer) (out : ReadState),
      CanonicalZeroWitness f B ρ r top s out a ∧ stateCharge r out < stateCharge r s

/-- Generic over the progress supply at each genuinely reached prefix,
but fixed to the true dependent canonical zero witness, not an arbitrary
decreasing relation. -/
def ExactCanonicalStrictStopping : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat) (initial : ReadState),
    (∀ (seen : List (List Answer)) (s : ReadState),
      CanonicalTrace f B ρ r top seen initial s → ProgressAt f B ρ r top s) →
    ∃ (answers : List (List Answer)) (stopped : ReadState),
      CanonicalTrace f B ρ r top answers initial stopped ∧ StopsAt f B ρ r top stopped

def ExactFundedCanonicalStoppingTrace : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r top : Nat) (initial : ReadState),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    PaidGlobalTail B r ρ (syntaxOf initial) → PaidComparisonCeiling B r ρ (syntaxOf initial) →
    ∃ (answers : List (List Answer)) (rawAnswers : List (List Nat)) (stopped : ReadState),
      CanonicalTrace f B ρ r top answers initial stopped ∧ StopsAt f B ρ r top stopped ∧
      rawAnswers = encodeAnswers answers ∧
      replay answers (eraseState initial) = some (eraseState stopped) ∧
      liftedReads f ρ stopped.reads ∧ RankBound r top stopped ∧ LongState stopped ∧
      OriginalRanks initial.reads stopped.reads ∧
      stateValue initial = stateValue stopped ∧
      rawAnswers.length + stateCharge r stopped ≤ stateCharge r initial

def FullActualCanonicalStoppingTrace : Prop :=
  ExactCanonicalProgressSplit ∧ ExactCanonicalStrictStopping ∧ ExactFundedCanonicalStoppingTrace

end LogicLineages.PermittedControl.ActualCanonicalStoppingTrace
