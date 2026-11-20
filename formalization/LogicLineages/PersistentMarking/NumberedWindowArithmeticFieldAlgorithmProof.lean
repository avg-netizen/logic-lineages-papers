import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmTargets
import LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmProof
open NumberedWindowArithmeticFields
open NumberedWindowFieldAlgorithm
open NumberedWindowArithmeticFieldAlgorithmTargets

private theorem noneSteps (fuel : Nat) : steps fuel none = none := by
  induction fuel with
  | zero => rfl
  | succ n ih => exact ih

private theorem doneSteps (fuel : Nat) (acc : List Nat) :
    steps fuel (some (0, acc)) = some (0, acc) := by
  induction fuel with
  | zero => rfl
  | succ n ih => exact ih

theorem fuelAgreement : ExactFieldFuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro code acc
    cases code <;> simp [steps, finish, decodeFieldsFuel]
  | succ n ih =>
    intro code acc
    cases code with
    | zero => simp [doneSteps, finish, decodeFieldsFuel]
    | succ c =>
      simp only [steps, step, decodeFieldsFuel, NumberedWindowActualPairAlgorithmChecks.currentDecoder]
      cases h : NumberedWindowPairAlgorithm.decode c with
      | none => simp [noneSteps, finish]
      | some p =>
        obtain ⟨a, b⟩ := p
        change finish (steps n (some (b, a :: acc))) = _
        rw [ih]
        cases hb : decodeFieldsFuel n b <;> simp [hb, List.reverse_cons, List.append_assoc]

private theorem packAgreement (xs : List Nat) : encodeFields xs = pack xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeFields, pack, ih, NumberedWindowActualPairAlgorithmChecks.currentPair]

private theorem unpackAgreement (c : Nat) : decodeFields c = unpack c := by
  simpa [unpack, decodeFields] using (fuelAgreement c c []).symm

theorem fields : ExactOrderedFieldCodec := ⟨funext packAgreement, funext unpackAgreement⟩

theorem nodes : ExactTaggedNodeCodec := by
  constructor
  · funext tag xs
    simp [encodeNode, packNode, packAgreement, NumberedWindowActualPairAlgorithmChecks.currentPair]
  · funext c
    cases c with
    | zero => rfl
    | succ n =>
      simp [decodeNode, unpackNode, NumberedWindowActualPairAlgorithmChecks.currentDecoder, unpackAgreement]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmProof
