module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalExecutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalCompletionProof
open OriginalLambdaTraversal OriginalLambdaTraversalSemanticProof
open OriginalLambdaTraversalWeightProof OriginalLambdaTraversalMeaningProof OriginalLambdaTraversalExecutionProof

theorem completed (leaf : Nat → Nat → Nat) (value parameter : Nat)
    (results : List Nat) (count : Nat) (hc : fuelValue value ≤ count) :
    stateIterate leaf count (⟨1, [visitValue value parameter], results⟩ : State) =
      (⟨1, [], semanticFold leaf value parameter :: results⟩ : State) := by
  have hw : workWeight [visitValue value parameter] ≤ count := by
    simpa [workWeightCons, visitWeight, workWeight] using hc
  have ht := liveSufficientFuel leaf count
    (⟨1, [visitValue value parameter], results⟩ : State) rfl hw
  apply terminalResult leaf _ _ ht
  rw [iterateMeaning]
  simp [stateMeaning, workMeaning, visitValue]

theorem initialEncoded (value parameter : Nat) :
    initialValue value parameter = encodeState (⟨1, [visitValue value parameter], []⟩ : State) := by
  simp [initialValue, encodeState, InternalApplicationResultStack.encodeState,
    NumberedMultisetNumeric.numbersNumber, Nat.add_comm 1]

theorem actualOriginalLambdaTraversalNativeTermination :
    OriginalLambdaTraversalTargets.ActualOriginalLambdaTraversalNativeTermination := by
  intro leaf value parameter count hc
  refine ⟨semanticFold leaf value parameter, ?_⟩
  rw [initialEncoded, encodedIteration, completed leaf value parameter [] count hc]

theorem runSingleton (leaf : Nat → Nat → Nat) (value parameter : Nat) :
    runValue leaf value parameter =
      encodeState (⟨1, [], [semanticFold leaf value parameter]⟩ : State) := by
  rw [runValue, initialEncoded, encodedIteration,
    completed leaf value parameter [] (fuelValue value) (Nat.le_refl _)]

theorem outputSingleton (value : Nat) :
    outputValue (encodeState (⟨1, [], [value]⟩ : State)) = value := by
  simp [outputValue, encodeState, InternalApplicationResultStack.encodeState,
    NumberedMultisetNumeric.numbersNumber, Nat.add_comm 1]

theorem foldSemantic (leaf : Nat → Nat → Nat) (value parameter : Nat) :
    foldValue leaf value parameter = semanticFold leaf value parameter := by
  rw [foldValue, runSingleton, outputSingleton]

theorem actualOriginalLambdaTraversalNativeRecurrence :
    OriginalLambdaTraversalTargets.ActualOriginalLambdaTraversalNativeRecurrence := by
  intro leaf value parameter
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    rw [foldSemantic, semanticEquation, if_pos ha, foldSemantic, foldSemantic]
  · intro hl
    have ha : tagValue value ≠ 2 := by omega
    rw [foldSemantic, semanticEquation, if_neg ha, if_pos hl, foldSemantic]
  · intro ha hl
    rw [foldSemantic, semanticEquation, if_neg ha, if_neg hl]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalCompletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalCompletionProof
