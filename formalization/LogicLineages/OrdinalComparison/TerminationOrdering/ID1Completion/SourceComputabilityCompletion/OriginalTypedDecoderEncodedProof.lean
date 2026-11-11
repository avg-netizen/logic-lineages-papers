module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEncodedProof
open OriginalTypedDecoder NumberedMultisetNumeric

 theorem encodedAppend (children rest : List Nat) :
    children.foldr (fun child tail => 1 + Nat.pair child tail) (numbersNumber rest) =
      numbersNumber (children ++ rest) := by
  induction children with
  | nil => rfl
  | cons child children ih => simpa only [List.foldr_cons, List.cons_append, numbersNumber] using congrArg (fun tail => 1 + Nat.pair child tail) ih

 theorem encodedTransition (H : Nat → Nat) (state : State) :
    transitionValue H (encodeState state) = encodeState (stateStep H state) := by
  have hz : Nat.pair 0 0 = 0 := rfl
  rcases state with ⟨s,work⟩
  by_cases hs : s = 1
  · subst s
    cases work with
    | nil => simp [transitionValue, encodeState, stateStep, numbersNumber]
    | cons request rest =>
      cases he : expandValue H request <;>
        simp [transitionValue, encodeState, stateStep, numbersNumber, he,
          failedState, hz, Nat.add_comm 1] <;>
          simpa only [Nat.add_comm 1] using encodedAppend _ _
  · simp [transitionValue, encodeState, stateStep, hs, failedState, numbersNumber, hz]

 theorem failedFixed (H : Nat → Nat) : transitionValue H 0 = 0 := by
  simp [transitionValue]

 theorem emptyFixed (H : Nat → Nat) : transitionValue H (Nat.pair 1 0) = Nat.pair 1 0 := by
  simp [transitionValue]

 theorem iterateAdd (H : Nat → Nat) (first second initial : Nat) :
    iterateValue H (first + second) initial = iterateValue H second (iterateValue H first initial) := by
  induction second with
  | zero => rfl
  | succ second ih =>
    change transitionValue H (iterateValue H (first + second) initial) =
      transitionValue H (iterateValue H second (iterateValue H first initial))
    exact congrArg (transitionValue H) ih

 theorem iterateSuccStart (H : Nat → Nat) (count initial : Nat) :
    iterateValue H (count + 1) initial = iterateValue H count (transitionValue H initial) := by
  simpa [iterateValue, Nat.add_comm 1] using iterateAdd H 1 count initial

 theorem failedIteration (H : Nat → Nat) (count : Nat) : iterateValue H count 0 = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change transitionValue H (iterateValue H count 0) = 0
    rw [ih, failedFixed]

 theorem emptyIteration (H : Nat → Nat) (count : Nat) :
    iterateValue H count (Nat.pair 1 0) = Nat.pair 1 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change transitionValue H (iterateValue H count (Nat.pair 1 0)) = Nat.pair 1 0
    rw [ih, emptyFixed]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEncodedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEncodedProof
