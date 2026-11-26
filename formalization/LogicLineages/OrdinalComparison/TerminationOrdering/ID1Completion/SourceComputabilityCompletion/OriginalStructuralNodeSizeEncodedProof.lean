module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeSemanticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeEncodedProof
open OriginalRawSyntaxTransport NumberedMultisetNumeric
open OriginalStructuralNodeSizeSemanticProof

 theorem encodedTransition (state : State) :
    OriginalStructuralNodeSize.transitionValue (encodeState state) =
      encodeState (OriginalStructuralNodeSizeSemanticProof.stateStep state) := by
  have hz : Nat.pair 0 0 = 0 := rfl
  rcases state with ⟨s, xs, ys⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => simp [OriginalStructuralNodeSize.transitionValue, encodeState, InternalApplicationResultStack.encodeState, numbersNumber, OriginalStructuralNodeSizeSemanticProof.stateStep]
    | cons frame rest =>
      by_cases ht : (Nat.unpair frame).1 = 0
      · by_cases h1 : arityValue (Nat.unpair (Nat.unpair (Nat.unpair frame).2).2).2 = 1 <;>
          by_cases h2 : arityValue (Nat.unpair (Nat.unpair (Nat.unpair frame).2).2).2 = 2 <;>
          simp [OriginalStructuralNodeSize.transitionValue, encodeState, InternalApplicationResultStack.encodeState,
            numbersNumber, OriginalStructuralNodeSizeSemanticProof.stateStep, ht, h1, h2, Nat.add_comm 1]
      · by_cases hf : (Nat.unpair frame).1 = 1
        · by_cases h1 : arityValue (Nat.unpair frame).2 = 1
          · cases ys <;>
              simp [OriginalStructuralNodeSize.transitionValue, encodeState, InternalApplicationResultStack.encodeState,
                numbersNumber, OriginalStructuralNodeSizeSemanticProof.stateStep, ht, hf, h1, failedState,
                InternalApplicationResultStack.failedState, hz, Nat.add_comm 1]
          · by_cases h2 : arityValue (Nat.unpair frame).2 = 2
            · cases ys with
              | nil => simp [OriginalStructuralNodeSize.transitionValue, encodeState, InternalApplicationResultStack.encodeState,
                  numbersNumber, OriginalStructuralNodeSizeSemanticProof.stateStep, ht, hf, h1, h2, failedState,
                  InternalApplicationResultStack.failedState, hz]
              | cons second ys =>
                cases ys <;>
                  simp [OriginalStructuralNodeSize.transitionValue, encodeState, InternalApplicationResultStack.encodeState,
                    numbersNumber, OriginalStructuralNodeSizeSemanticProof.stateStep, ht, hf, h1, h2, failedState,
                    InternalApplicationResultStack.failedState, hz, Nat.add_comm 1]
            · simp [OriginalStructuralNodeSize.transitionValue, encodeState, InternalApplicationResultStack.encodeState,
                numbersNumber, OriginalStructuralNodeSizeSemanticProof.stateStep, ht, hf, h1, h2, failedState,
                InternalApplicationResultStack.failedState, hz, Nat.add_comm 1]
        · simp [OriginalStructuralNodeSize.transitionValue, encodeState, InternalApplicationResultStack.encodeState,
            numbersNumber, OriginalStructuralNodeSizeSemanticProof.stateStep, ht, hf, failedState, InternalApplicationResultStack.failedState,
            hz, Nat.add_comm 1]
  · simp [OriginalStructuralNodeSize.transitionValue, encodeState, InternalApplicationResultStack.encodeState,
      numbersNumber, OriginalStructuralNodeSizeSemanticProof.stateStep, hs, failedState, InternalApplicationResultStack.failedState, hz]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeEncodedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeEncodedProof
