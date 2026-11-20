import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTyCodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmProof
open NumberedWindowAddressAlgorithm NumberedWindowArithmeticAddressAlgorithmTargets
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTyCodeProof
open NumberedWindowArithmeticBinderCode NumberedWindowArithmeticFields NumberedWindowArithmeticClassAddress
open NumberedWindowArithmeticCodecLaws NumberedWindowArithmeticFieldAlgorithmChecks

private theorem adequate (f c : Nat) (hc : c ≤ f) : decodeTyFuel f c = decodeTy c := by
  cases h : decodeTy c with
  | some t =>
    have e := decodeSound h
    rw [← e] at hc ⊢
    exact complete f t hc
  | none =>
    cases z : decodeTyFuel f c with
    | none => rfl
    | some t =>
      have e := sound f c t z
      rw [← e, roundtrip] at h
      contradiction

private theorem next (n : Nat) : nextType n ((List.range n).map (fun i => (decodeTy i).isSome)) =
    (decodeTy n).isSome := by
  cases n with
  | zero => rfl
  | succ m =>
    simp only [nextType, ← NumberedWindowActualPairAlgorithmChecks.currentDecoder]
    change _ = (decodeTyFuel (m+1) (m+1)).isSome
    simp only [decodeTyFuel]
    cases hd : NumberedWindowArithmeticPair.decode m with
    | none => rfl
    | some p =>
      obtain ⟨a,b⟩ := p
      have bounds := pairBounds a b
      rw [pairRead hd] at bounds
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (Nat.lt_succ_of_le bounds.1), List.getElem?_range (Nat.lt_succ_of_le bounds.2),
        Option.map_some, Option.getD_some]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [adequate m a bounds.1, adequate m b bounds.2]
      cases decodeTy a <;> cases decodeTy b <;> rfl

theorem table : ExactTypeTable := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => simp [typeTable, ih, List.range_succ, next]

theorem typeGuard : ExactTypeGuard := fun n => by simpa [typeBit, table n] using next n

private def guardStack (xs : List Nat) : Option (List Nat) :=
  if xs.all typeBit then some xs else none

private theorem bindFuel (f c : Nat) : (decodeFieldsFuel f c).bind guardStack =
    (decodeBindersFuel f c).map (List.map encodeTy) := by
  induction f generalizing c with
  | zero =>
    cases c <;> rfl
  | succ m ih =>
    cases c with
    | zero => rfl
    | succ n =>
      simp only [decodeFieldsFuel,decodeBindersFuel]
      cases hp : NumberedWindowArithmeticPair.decode n with
      | none => rfl
      | some p =>
        rcases p with ⟨a,b⟩
        have rest := ih b
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases hA : decodeTy a <;> cases hf : decodeFieldsFuel m b <;> cases hb : decodeBindersFuel m b
        all_goals try have en := decodeSound hA
        all_goals simp [hf,hb,hA,guardStack,typeGuard a] at rest ⊢
        all_goals grind

theorem context : ExactBinderView := by
  intro n
  unfold contextView
  rw [← exact_ExactOrderedFieldCodec.2]
  exact bindFuel n n

theorem addr : ExactAddressView := by
  intro n
  unfold addressView decodeAddress
  rw [← exact_ExactTaggedNodeCodec.2]
  cases hn : decodeNode n with
  | none => rfl
  | some p =>
    rcases p with ⟨tag,xs⟩
    fun_cases assembleAddress tag xs
    case case1 ctx t k =>
      simp only [Option.bind_eq_bind, Option.bind_some, assembleAddress]
      rw [context ctx, typeGuard t]
      cases hc : decodeBinders ctx <;> cases ht : decodeTy t
      all_goals try have en := decodeSound ht
      all_goals simp_all [address]
    case case2 bad =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      unfold assembleAddress
      split <;> split <;> first | rfl | grind

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmProof
