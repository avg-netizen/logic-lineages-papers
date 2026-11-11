module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEncodedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalTypedDecoder OriginalTypedDecoderEncodedProof

/-- This invariant recovers original syntax from any successful raw run. It
has no typed-input, decoded-context, canonicality or sufficient-fuel premise. -/
theorem successfulWork (n : Nat) (arity : Fin n → Nat) (fuel : Nat) (work : List Nat)
    (h : finishedValue (iterateValue (headSignatureValue n arity) fuel
      (encodeState ⟨1,work⟩)) = 1) :
    ∀ request ∈ work, ∃ code : Code (Fin n), codeNumber code = requestRaw request := by
  induction fuel generalizing work with
  | zero =>
    cases work with
    | nil => simp
    | cons request rest =>
      simp [iterateValue,finishedValue,encodeState,numbersNumber] at h
  | succ fuel ih =>
    cases work with
    | nil => simp
    | cons request rest =>
      rw [iterateSuccStart,encodedTransition] at h
      cases he : expandValue (headSignatureValue n arity) request with
      | none =>
        simp [stateStep,he,failedState,encodeState,numbersNumber,
          (show Nat.pair 0 0 = 0 from rfl),failedIteration,finishedValue] at h
      | some children =>
        have hn : finishedValue (iterateValue (headSignatureValue n arity) fuel
            (encodeState ⟨1,children ++ rest⟩)) = 1 := by
          simpa [stateStep,he] using h
        have hall := ih (children ++ rest) hn
        intro item hi
        rcases List.mem_cons.mp hi with hi | hi
        · rw [hi]
          exact OriginalTypedDecoderReconstructionLocalProof.expansionReconstruct
            n arity request children he (fun child hc => hall child (List.mem_append_left rest hc))
        · exact hall item (List.mem_append_right children hi)

theorem successfulCheck (n : Nat) (arity : Fin n → Nat) (request : Nat)
    (h : checkValue (headSignatureValue n arity) request = 1) :
    ∃ code : Code (Fin n), codeNumber code = requestRaw request := by
  apply successfulWork n arity (requestRaw request+1) [request]
    (by simpa only [checkValue,initialValue,encodeState,numbersNumber] using h)
    request (by simp)

theorem checkBit (H : Nat → Nat) (request : Nat) :
    checkValue H request = 0 ∨ checkValue H request = 1 := by
  unfold checkValue finishedValue
  split <;> simp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionProof
