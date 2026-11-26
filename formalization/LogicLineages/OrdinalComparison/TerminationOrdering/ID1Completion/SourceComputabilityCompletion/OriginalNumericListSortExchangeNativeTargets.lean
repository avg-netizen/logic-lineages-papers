module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeTargets
open OriginalNumericListSortExchangeNative NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
/-- Native constructive completeness only. The witness is an explicit list
of literal swaps and its actual checker evaluation; no internal derivation
or source BASE certificate follows by reflection from this theorem. -/
def PermutationPath : Prop := ∀ (xs ys : List Nat), xs.Perm ys →
 ∃ moves : List Move, Trace xs ys moves ∧
 evaluate (InternalPathChecker.checker OriginalNumericListSortExchange.edge false)
   (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ pathCode moves ::ᵥ nil) = 1
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeTargets
