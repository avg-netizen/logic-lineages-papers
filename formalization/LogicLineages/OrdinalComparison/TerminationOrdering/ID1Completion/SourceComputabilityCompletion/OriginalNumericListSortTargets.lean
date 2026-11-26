module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric OriginalNumericListSort
/-- Exact native encoded-list result, not internal arithmetic reflection. -/
def NativeCalibration : Prop := ∀ xs : List Nat,
  evaluate sort (numbersNumber xs ::ᵥ List.Vector.nil) = numbersNumber (xs.insertionSort (· ≤ ·))
/-- Native completeness and invariance, preserving multiplicities rather
than only membership. No typed BASE reconstruction or runtime tuple change. -/
def NativePermutation : Prop := ∀ xs ys : List Nat,
  evaluate sort (numbersNumber xs ::ᵥ List.Vector.nil) =
    evaluate sort (numbersNumber ys ::ᵥ List.Vector.nil) ↔ xs.Perm ys
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortTargets
