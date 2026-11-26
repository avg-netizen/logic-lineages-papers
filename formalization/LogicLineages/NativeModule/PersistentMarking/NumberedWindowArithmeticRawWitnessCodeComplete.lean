module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRawRootCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeComplete
open NumberedWindowRawWitnessBits
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticRawRootCodeProof

private theorem positive (w : RawWitness) : 0 < encodeWitness w := by
  cases w <;> exact nodePos _ _

private theorem childFuel (tag : Nat) (fields : List Nat) (v : RawWitness) (fuel : Nat)
    (h : encodeNode tag fields ≤ fuel+1) (hv : encodeWitness v ∈ fields) :
    encodeWitness v ≤ fuel :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (nodeBelow tag fields (encodeWitness v) hv) h)

theorem atFuel (fuel : Nat) : ∀ w, encodeWitness w ≤ fuel →
    decodeWitnessFuel fuel (encodeWitness w) = some w := by
  induction fuel with
  | zero =>
    intro w h
    exact False.elim ((Nat.not_lt_of_ge h) (positive w))
  | succ fuel ih =>
    intro w h
    cases w with
    | root v => simp [encodeWitness,decodeWitnessFuel,nodeRound,assembleWitness,rootRound]
    | lam v =>
      have hv := ih v (childFuel 1 [encodeWitness v] v fuel h (by simp))
      simp [encodeWitness,decodeWitnessFuel,nodeRound,assembleWitness,hv]
    | ordinaryBase i v =>
      have hv := ih v (childFuel 2 [i,encodeWitness v] v fuel h (by simp))
      simp [encodeWitness,decodeWitnessFuel,nodeRound,assembleWitness,hv]
    | numberedBase i v =>
      have hv := ih v (childFuel 3 [i,encodeWitness v] v fuel h (by simp))
      simp [encodeWitness,decodeWitnessFuel,nodeRound,assembleWitness,hv]
    | numberedExtra i v =>
      have hv := ih v (childFuel 4 [i,encodeWitness v] v fuel h (by simp))
      simp [encodeWitness,decodeWitnessFuel,nodeRound,assembleWitness,hv]
    | auxFunction v =>
      have hv := ih v (childFuel 5 [encodeWitness v] v fuel h (by simp))
      simp [encodeWitness,decodeWitnessFuel,nodeRound,assembleWitness,hv]

theorem roundtrip (w : RawWitness) : decodeWitness (encodeWitness w) = some w :=
  atFuel (encodeWitness w) w (Nat.le_refl _)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeComplete
