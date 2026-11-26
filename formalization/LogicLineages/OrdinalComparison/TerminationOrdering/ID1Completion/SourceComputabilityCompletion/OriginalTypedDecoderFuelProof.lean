module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEncodedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderFuelProof
open OriginalTypedDecoder OriginalTypedDecoderWeightProof OriginalTypedDecoderEncodedProof
open NumberedMultisetNumeric

 theorem sufficientWorkFuel (H : Nat → Nat) (count : Nat) :
    ∀ work : List Nat, workWeight work ≤ count →
      iterateValue H count (encodeState ⟨1,work⟩) = 0 ∨
        iterateValue H count (encodeState ⟨1,work⟩) = Nat.pair 1 0 := by
  induction count with
  | zero =>
    intro work hb
    cases work with
    | nil => exact Or.inr rfl
    | cons request rest =>
      rw [workWeightCons] at hb
      unfold requestWeight at hb
      omega
  | succ count ih =>
    intro work hb
    cases work with
    | nil => exact Or.inr (emptyIteration H (count + 1))
    | cons request rest =>
      rw [iterateSuccStart, encodedTransition]
      cases he : expandValue H request with
      | none =>
        simp only [stateStep, if_true, he]
        exact Or.inl (failedIteration H count)
      | some children =>
        simp only [stateStep, if_true, he]
        apply ih
        have hd := expansionDecrease H request children he
        rw [workWeightCons] at hb
        rw [workWeightAppend]
        omega

 theorem singletonFuel (H : Nat → Nat) (request count : Nat)
    (h : requestRaw request + 1 ≤ count) :
    iterateValue H count (initialValue request) = 0 ∨
      iterateValue H count (initialValue request) = Nat.pair 1 0 := by
  apply sufficientWorkFuel H count [request]
  simpa [workWeightCons, workWeightNil, requestWeight] using h

 theorem actualOriginalTypedFuel : OriginalTypedDecoderTargets.ActualOriginalTypedFuel :=
  ⟨expansionDecrease, workDecrease, singletonFuel⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderFuelProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderFuelProof
