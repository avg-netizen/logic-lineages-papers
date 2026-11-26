module
public import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalNodeProgress
open OrdinalComparison PreparedProjection
open ActualReadChargeIteration (ReadState RankBound ActiveAt NodeGuards stateValue stateCharge)
open ActualCanonicalOperandGrouping ActualCanonicalZeroTrace
open ActualZeroClassReplacement ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open ActualFullValueLabels ActualFullLabelPairGuards ActualFiniteFullValueGuards ActualFullValueMaximalMetadata
open ActualFiniteGlobalTail ActualGlobalComparisonCeiling
open ActualZeroClassCohortTransfer

/-- Outcome of the actual nonlinear branch. The finite comparison
conjunction holds at the same original valuation and real tied slots;
the maximal signed coefficient is exact, irrespective of its sign. -/
def NonlinearOutcome (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
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
    ((maximalCoefficient terms a ≠ 0 ∧
        2 * stateValue s = maximalCoefficient terms a * (C : Int) +
          2 * (s.constant + (rowParts f C terms vals anns).2)) ∨
      (maximalCoefficient terms a = 0 ∧ ∃ out : ReadState,
        CanonicalZeroWitness f B ρ r top s out a ∧ stateCharge r out < stateCharge r s))

def ProgressAt (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat) (s : ReadState) : Prop :=
  ∃ xs, normalizeCanonical f ρ s.reads = some xs ∧ liftedReads f ρ xs ∧
    (¬ ActiveAt top xs ∨ (ActiveAt top xs ∧ NonlinearOutcome f B ρ r top s xs))

/-- Inactive highest stays a separate genuine alternative; no claim
about linear projection or a sign cutoff is included in this layer. -/
def ExactCanonicalLocalProgress : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r top : Nat) (s : ReadState), liftedReads f ρ s.reads → RankBound r top s →
    (∀ xs : List Read, normalizeCanonical f ρ s.reads = some xs → ActiveAt top xs →
      let ls := labels (xs.map Prod.fst)
      NodeGuards B ρ xs ∧ ReadyFamily B ρ top ls ∧ PaidFamily B ρ top (ρ top) ls) →
    ProgressAt f B ρ r top s

def ExactCanonicalReachedProgress : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r top : Nat) (initial reached : ReadState) (answers : List (List Answer)),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    PaidGlobalTail B r ρ (syntaxOf initial) → PaidComparisonCeiling B r ρ (syntaxOf initial) →
    CanonicalTrace f B ρ r top answers initial reached →
    ProgressAt f B ρ r top reached

def FullActualCanonicalNodeProgress : Prop :=
  ExactCanonicalLocalProgress ∧ ExactCanonicalReachedProgress

end LogicLineages.PermittedControl.ActualCanonicalNodeProgress
