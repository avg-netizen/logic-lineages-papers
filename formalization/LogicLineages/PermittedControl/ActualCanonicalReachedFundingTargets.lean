module
public import LogicLineages.PermittedControl.ActualCanonicalZeroAlphabetTargets
public import LogicLineages.PermittedControl.ActualGlobalComparisonCeilingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalReachedFunding
open OrdinalComparison PreparedProjection
open ActualCanonicalZeroTrace ActualCanonicalOperandGrouping
open ActualReadChargeIteration (ReadState RankBound ActiveAt NodeGuards)
open ActualZeroClassReplacement (Read liftedReads)
open ActualZeroClassOutputState (OriginalRanks)
open ActualZeroEdgeAlphabet (Covers)
open ActualFiniteGlobalTail
open ActualGlobalComparisonCeiling (PaidComparisonCeiling)
open ActualFiniteFullValueGuards (ReadyFamily PaidFamily)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Answer)

def ExactCanonicalReachFacts : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (initial reached : ReadState) (answers : List (List Answer)),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    CanonicalTrace f B ρ r top answers initial reached →
    liftedReads f ρ reached.reads ∧ RankBound r top reached ∧ LongState reached ∧
    OriginalRanks initial.reads reached.reads ∧ Covers (globalAlphabet r (syntaxOf initial)) reached

/-- One static transfer payment and the ORIGINAL long-shape premise
cover the actual canonical reached snapshot, not an arbitrary derived
syntax candidate. -/
def ExactCanonicalTransferFunding : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (initial reached : ReadState) (answers : List (List Answer)),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    PaidGlobalTail B r ρ (syntaxOf initial) →
    CanonicalTrace f B ρ r top answers initial reached →
    ∀ xs : List Read, normalizeCanonical f ρ reached.reads = some xs → NodeGuards B ρ xs

/-- The original explicit comparisons and transfer ceilings are
separate numerical inputs. The true active highest occurrence pays the
greatest coordinate; the wholly linear/empty case is not forced to pay. -/
def ExactCanonicalReachedFunding : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ baseline : Nat → Nat) (r top : Nat) (initial reached : ReadState) (answers : List (List Answer)),
    StrictMono ρ → (∀ i : Nat, i < top → baseline i = ρ i) →
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    PaidGlobalTail B r ρ (syntaxOf initial) → PaidComparisonCeiling B r ρ (syntaxOf initial) →
    CanonicalTrace f B ρ r top answers initial reached →
    ∀ xs : List Read, normalizeCanonical f ρ reached.reads = some xs → ActiveAt top xs →
      let ls := labels (xs.map Prod.fst)
      NodeGuards B ρ xs ∧ ReadyFamily B baseline top ls ∧ PaidFamily B baseline top (ρ top) ls

def FullActualCanonicalReachedFunding : Prop :=
  ExactCanonicalReachFacts ∧ ExactCanonicalTransferFunding ∧ ExactCanonicalReachedFunding

end LogicLineages.PermittedControl.ActualCanonicalReachedFunding
