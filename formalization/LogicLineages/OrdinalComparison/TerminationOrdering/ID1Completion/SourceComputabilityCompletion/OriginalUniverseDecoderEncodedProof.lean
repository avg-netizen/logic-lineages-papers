module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEncodedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderEncodedProof
open OriginalUniverseDecoder NumberedMultisetNumeric
open OriginalTypedDecoder (encodeState failedState finishedValue)

theorem encodedTransition (H : Nat → Nat) (M W : Nat → Nat → Nat) (context : Nat)
    (state : OriginalTypedDecoder.State) :
    transitionValue H M W (encodeState state) context = encodeState (stateStep H M W context state) := by
  rcases state with ⟨s,work⟩
  by_cases hs : s = 1
  · subst s
    cases work with
    | nil => simp [transitionValue,stateStep,encodeState,numbersNumber]
    | cons request rest =>
      by_cases hg : guardValue M W request context = 1
      · simpa [transitionValue,stateStep,encodeState,numbersNumber,hg,Nat.add_comm 1]
          using OriginalTypedDecoderEncodedProof.encodedTransition H ⟨1,request :: rest⟩
      · simp [transitionValue,stateStep,encodeState,numbersNumber,hg,failedState,Nat.add_comm 1,(show Nat.pair 0 0 = 0 from rfl)]
  · simp [transitionValue,stateStep,encodeState,numbersNumber,hs,failedState,(show Nat.pair 0 0 = 0 from rfl)]

theorem failedFixed (H : Nat → Nat) (M W : Nat → Nat → Nat) (context : Nat) :
    transitionValue H M W 0 context = 0 := by simp [transitionValue]

theorem emptyFixed (H : Nat → Nat) (M W : Nat → Nat → Nat) (context : Nat) :
    transitionValue H M W (Nat.pair 1 0) context = Nat.pair 1 0 := by simp [transitionValue]

theorem iterateAdd (H : Nat → Nat) (M W : Nat → Nat → Nat) (first second initial context : Nat) :
    iterateValue H M W (first+second) initial context =
      iterateValue H M W second (iterateValue H M W first initial context) context := by
  induction second with
  | zero => rfl
  | succ second ih =>
    change transitionValue H M W (iterateValue H M W (first+second) initial context) context =
      transitionValue H M W (iterateValue H M W second (iterateValue H M W first initial context) context) context
    rw [ih]

theorem iterateSuccStart (H : Nat → Nat) (M W : Nat → Nat → Nat) (count initial context : Nat) :
    iterateValue H M W (count+1) initial context =
      iterateValue H M W count (transitionValue H M W initial context) context := by
  simpa [iterateValue,Nat.add_comm 1] using iterateAdd H M W 1 count initial context

theorem failedIteration (H : Nat → Nat) (M W : Nat → Nat → Nat) (count context : Nat) :
    iterateValue H M W count 0 context = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change transitionValue H M W (iterateValue H M W count 0 context) context = 0
    rw [ih,failedFixed]

theorem emptyIteration (H : Nat → Nat) (M W : Nat → Nat → Nat) (count context : Nat) :
    iterateValue H M W count (Nat.pair 1 0) context = Nat.pair 1 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change transitionValue H M W (iterateValue H M W count (Nat.pair 1 0) context) context = Nat.pair 1 0
    rw [ih,emptyFixed]

/-- The guarded step is either the SAME old typed step or literal failure. -/
theorem transitionRefines (H : Nat → Nat) (M W : Nat → Nat → Nat) (state context : Nat) :
    transitionValue H M W state context = 0 ∨
      transitionValue H M W state context = OriginalTypedDecoder.transitionValue H state := by
  unfold transitionValue
  by_cases hs : (Nat.unpair state).1 = 1
  · rw [if_pos hs]
    by_cases hw : (Nat.unpair state).2 = 0
    · rw [if_pos hw]
      exact Or.inr (by simp [OriginalTypedDecoder.transitionValue,hs,hw])
    · rw [if_neg hw]
      split <;> simp
  · simp [hs]

/-- At every fuel, rejection is the only possible extra behavior. -/
theorem iterateRefines (H : Nat → Nat) (M W : Nat → Nat → Nat) (fuel initial context : Nat) :
    iterateValue H M W fuel initial context = 0 ∨
      iterateValue H M W fuel initial context = OriginalTypedDecoder.iterateValue H fuel initial := by
  induction fuel with
  | zero => exact Or.inr rfl
  | succ fuel ih =>
    change transitionValue H M W (iterateValue H M W fuel initial context) context = 0 ∨
      transitionValue H M W (iterateValue H M W fuel initial context) context =
        OriginalTypedDecoder.transitionValue H (OriginalTypedDecoder.iterateValue H fuel initial)
    rcases ih with h | h
    · exact Or.inl (by rw [h,failedFixed])
    · rw [h]
      exact transitionRefines H M W _ context

theorem acceptanceImpliesTyped (H : Nat → Nat) (M W : Nat → Nat → Nat) (fuel initial context : Nat)
    (h : finishedValue (iterateValue H M W fuel initial context) = 1) :
    finishedValue (OriginalTypedDecoder.iterateValue H fuel initial) = 1 := by
  rcases iterateRefines H M W fuel initial context with hz | he
  · simp [hz,finishedValue] at h
  · rwa [he] at h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderEncodedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderEncodedProof
