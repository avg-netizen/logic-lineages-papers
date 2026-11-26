module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber decodeNumbers)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalFunctionalRawRepack (repack)
open NumberedWindowFieldAlgorithm (pack)

private theorem foldPack (xs : List Nat) :
    xs.foldr (fun a b => evaluate fieldCons (a ::ᵥ b ::ᵥ nil)) 0 = pack xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldr_cons, ih, NumberedWindowInternalSparsePairEvaluationProof.consValue]
    rfl

/-- Numerical behavior at every original scratch code, with the decoder's
existing fallback untouched. -/
theorem exact_FunctionalRawRepackValue (c : Nat) :
    evaluate repack (c ::ᵥ nil) = pack ((decodeNumbers c).getD []) := by
  rw [repack, actualRawListRecursionEvaluation]
  exact foldPack _

/-- The code of an actual input list needs no fallback. -/
theorem exact_FunctionalRawRepackOnList (xs : List Nat) :
    evaluate repack (numbersNumber xs ::ᵥ nil) = pack xs := by
  rw [exact_FunctionalRawRepackValue, numbersRoundTrip]
  rfl

theorem exact_FunctionalRawRepackTwoCell :
    evaluate repack (numbersNumber [2,3] ::ᵥ nil) = 228 := by
  rw [exact_FunctionalRawRepackOnList]
  rfl

#print axioms exact_FunctionalRawRepackValue
#print axioms exact_FunctionalRawRepackOnList
#print axioms exact_FunctionalRawRepackTwoCell
end LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackNumericProof
