module
public import Mathlib.Data.List.Count

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Finite vector of actual principal-occurrence counts, ordered from the
smallest principal (highest reverse weight) to the largest. -/
def ComparisonKernelHistogram : Nat → Type
  | 0 => PUnit
  | n+1 => Nat × ComparisonKernelHistogram n

/-- Drop rank zero, and decrease the remaining ranks by one. -/
def comparisonRankTail (word : List Nat) : List Nat :=
  word.filterMap (fun r => if r=0 then none else some (r-1))

def comparisonKernelHistogram : (m : Nat) → List Nat → ComparisonKernelHistogram m
  | 0, _ => PUnit.unit
  | m+1, word => (word.count 0,comparisonKernelHistogram m (comparisonRankTail word))

def ComparisonKernelHistogramLt : (m : Nat) → ComparisonKernelHistogram m → ComparisonKernelHistogram m → Prop
  | 0 => fun _ _ => False
  | m+1 => Prod.Lex Nat.lt (ComparisonKernelHistogramLt m)

/-- The source h-coordinate and the list of auxiliary kernel ranks. Masses
are intentionally absent from the measure, not from the semantic evaluator. -/
structure ComparisonRankState where
  heads : Nat
  kernels : List Nat

/-- Exact weighted-multiset pattern of source section8 combined steps.
This component does NOT assert that all actual source recursive children
have already been compiled or shown to satisfy these alternatives. -/
def ComparisonRankStep (m : Nat) (next current : ComparisonRankState) : Prop :=
  next.heads<current.heads ∨
    (next.heads=current.heads ∧ ∃ (before after added : List Nat) (r : Nat),
      r<m ∧ (∀ s∈added,r<s) ∧ current.kernels=before++r::after ∧
        next.kernels=before++added++after)

end LogicLineages.OrdinalComparison
