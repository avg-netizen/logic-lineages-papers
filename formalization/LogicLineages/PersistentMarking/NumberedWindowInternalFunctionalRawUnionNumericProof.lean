module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open ID1Completion.InternalApplicationValidityStackAppend (append appendStep)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactPredecessorEvaluation)
open NumberedWindowFieldAlgorithm (pack unpack)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput exact_OriginalUnpackCases)
open NumberedWindowInternalDirectTypedListTargets (parsedPayload)
open NumberedWindowInternalFunctionalRawUnion
open NumberedWindowInternalFunctionalRawRepack (repack)
open NumberedWindowInternalFunctionalRawRepackNumericProof (exact_FunctionalRawRepackOnList)

theorem exact_FunctionalUnionUnpackPack (xs : List Nat) : unpack (pack xs) = some xs := by
  induction xs with
  | nil => exact exact_OriginalUnpackCases.1
  | cons a xs ih =>
    rw [pack,exact_OriginalUnpackCases.2.2,ih]
    rfl

theorem exact_ScratchAppendOnLists (xs ys : List Nat) :
    evaluate append (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ nil) = numbersNumber (xs ++ ys) := by
  rw [append,actualRawListRecursionEvaluation,numbersRoundTrip]
  change xs.foldr (fun a b => evaluate appendStep (a ::ᵥ b ::ᵥ numbersNumber ys ::ᵥ nil))
    (numbersNumber ys) = numbersNumber (xs ++ ys)
  have h (a b : Nat) : evaluate appendStep (a ::ᵥ b ::ᵥ numbersNumber ys ::ᵥ nil) =
      1 + Nat.pair a b := consEvaluation a b
  simp only [h]
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons,List.cons_append,numbersNumber,ih]

theorem exact_ParsedPayloadOnList (raw : Nat) (xs : List Nat) (held : unpack raw = some xs) :
    evaluate parsedPayload (raw ::ᵥ nil) = numbersNumber xs := by
  unfold parsedPayload
  rw [evaluate,vectorOne]
  change evaluate predecessor (evaluate parser (raw ::ᵥ nil) ::ᵥ nil) = _
  rw [exact_ActualEncodedOutput,held,exactPredecessorEvaluation]
  simp [encodeResult]

private theorem sideValue (i : Fin 2) (xs : List.Vector Nat 2) (ls : List Nat)
    (p : unpack (xs.get i) = some ls) : evaluate (side i) xs = numbersNumber ls := by
  unfold side
  rw [evaluate,vectorOne]
  exact exact_ParsedPayloadOnList (xs.get i) ls p

/-- The actual binary program gives the uniquely ordered packed
concatenation on successful original raw lists. -/
theorem exact_FunctionalRawUnionNumeric (a b : Nat) (xs ys : List Nat)
    (pa : unpack a = some xs) (pb : unpack b = some ys) :
    evaluate functionalUnion (a ::ᵥ b ::ᵥ nil) = pack (xs ++ ys) := by
  unfold functionalUnion
  rw [evaluate,vectorOne]
  change evaluate repack (evaluate joinedScratch (a ::ᵥ b ::ᵥ nil) ::ᵥ nil) = _
  have joined : evaluate joinedScratch (a ::ᵥ b ::ᵥ nil) = numbersNumber (xs ++ ys) := by
    unfold joinedScratch
    rw [evaluate,vectorTwo]
    change evaluate append
      (evaluate (side 0) (a ::ᵥ b ::ᵥ nil) ::ᵥ evaluate (side 1) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil) = _
    rw [sideValue 0 (a ::ᵥ b ::ᵥ nil) xs pa,sideValue 1 (a ::ᵥ b ::ᵥ nil) ys pb]
    exact exact_ScratchAppendOnLists xs ys
  rw [joined,exact_FunctionalRawRepackOnList]

theorem exact_FunctionalUnionOnPacked (xs ys : List Nat) :
    evaluate functionalUnion (pack xs ::ᵥ pack ys ::ᵥ nil) = pack (xs ++ ys) :=
  exact_FunctionalRawUnionNumeric (pack xs) (pack ys) xs ys
    (exact_FunctionalUnionUnpackPack xs) (exact_FunctionalUnionUnpackPack ys)

#print axioms exact_FunctionalUnionUnpackPack
#print axioms exact_ScratchAppendOnLists
#print axioms exact_ParsedPayloadOnList
#print axioms exact_FunctionalRawUnionNumeric
#print axioms exact_FunctionalUnionOnPacked
end LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionNumericProof
