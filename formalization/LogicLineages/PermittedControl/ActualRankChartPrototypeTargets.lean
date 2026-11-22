module
public import LogicLineages.PermittedControl.ActualLowerRankChartRowsTargets
public import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankChartPrototype
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualFiniteOrderBranches (Pattern patterns guard rename realized)
open ActualLowerRankChartRows (LowerChartCondition)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixOrderBranches (branches)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalPrintedRankedLiteralHigh (cutoff PaidSupport chartMinimum)
open OriginalMatrixDenseRanks (support)

/-- Dense syntax may enumerate inconsistent duplicate names.
A genuine chart labels a literal source name only once. -/
def Consistent (branch : Pattern) : Prop :=
  ∀ a ∈ branch.2, ∀ b ∈ branch.2, a.1 = b.1 → a.2 = b.2

def readWithin (names : List Nat) (branch : Pattern) (lower outside : Nat → Nat)
    (z name : Nat) : Nat :=
  if name ∈ names then Function.update lower (top branch) z (rename branch name) else outside name

def seed (C : Nat) (branch : Pattern) (lower : Nat → Nat) : Nat :=
  max C (rankedPredecessor (top branch) lower)

def prototype (C : Nat) (names : List Nat) (branch : Pattern) (lower outside : Nat → Nat) : Nat → Nat :=
  readWithin names branch lower outside (seed C branch lower)

def ExactChartConsistency : Prop :=
  ∀ (θ : Nat → Nat) (branch : Pattern), (guard branch).eval θ → Consistent branch

def ExactPrototypeChart : Prop :=
  ∀ (C : Nat) (names : List Nat) (branch : Pattern), branch ∈ patterns names →
    0 < branch.1 → Consistent branch →
    ∀ (lower outside : Nat → Nat), LowerChartCondition C (top branch) lower →
      let θ := prototype C names branch lower outside
      (guard branch).eval θ ∧ (∀ name ∈ names, C ≤ θ name) ∧
      (∀ i ≤ top branch, realized θ branch i = Function.update lower (top branch) (seed C branch lower) i)

def ExactOriginalChartPrototype : Prop :=
  ∀ (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (branch : Pattern), branch ∈ branches known gates p →
      0 < branch.1 → Consistent branch →
      ∀ (lower outside : Nat → Nat), LowerChartCondition (cutoff B known gates p positive) (top branch) lower →
        let names := support (matrix known gates p)
        let C := cutoff B known gates p positive
        let θ := prototype C names branch lower outside
        (guard branch).eval θ ∧ PaidSupport B θ known gates p positive ∧
        chartMinimum B θ known gates p positive branch = seed C branch lower ∧
        (∀ i < top branch, realized θ branch i = lower i) ∧
        ∀ z : Nat, replay θ known gates p branch z = readWithin names branch lower outside z

def FullActualRankChartPrototype : Prop :=
  ExactChartConsistency ∧ ExactPrototypeChart ∧ ExactOriginalChartPrototype

end LogicLineages.PermittedControl.ActualRankChartPrototype
