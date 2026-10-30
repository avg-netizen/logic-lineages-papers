module

public import LogicLineages.ComputabilityKnowledge.OracleDecoderTargets
public import LogicLineages.ComputabilityKnowledge.OracleProgramProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleDecoderProof
open OracleProgram OracleDecoder OracleDecoderTargets

private theorem fuel_complete (p : Program) : ∀ fuel, encode p < fuel → decodeFuel fuel (encode p) = some p := by
  induction p with
  | base c =>
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel => simp [encode, tagged, decodeFuel, Nat.unpair_pair, Denumerable.ofNat_encode]
  | query =>
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel => simp [encode, tagged, decodeFuel, Nat.unpair_pair]
  | pair p q ihp ihq =>
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hp : encode p < fuel := by
            have := Nat.left_le_pair (encode p) (encode q)
            have := Nat.right_le_pair 2 (Nat.pair (encode p) (encode q))
            simp only [encode, tagged] at hf
            omega
          have hq : encode q < fuel := by
            have := Nat.right_le_pair (encode p) (encode q)
            have := Nat.right_le_pair 2 (Nat.pair (encode p) (encode q))
            simp only [encode, tagged] at hf
            omega
          simp [encode, tagged, decodeFuel, Nat.unpair_pair, ihp fuel hp, ihq fuel hq]
  | comp p q ihp ihq =>
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hp : encode p < fuel := by
            have := Nat.left_le_pair (encode p) (encode q)
            have := Nat.right_le_pair 3 (Nat.pair (encode p) (encode q))
            simp only [encode, tagged] at hf
            omega
          have hq : encode q < fuel := by
            have := Nat.right_le_pair (encode p) (encode q)
            have := Nat.right_le_pair 3 (Nat.pair (encode p) (encode q))
            simp only [encode, tagged] at hf
            omega
          simp [encode, tagged, decodeFuel, Nat.unpair_pair, ihp fuel hp, ihq fuel hq]
  | prec p q ihp ihq =>
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hp : encode p < fuel := by
            have := Nat.left_le_pair (encode p) (encode q)
            have := Nat.right_le_pair 4 (Nat.pair (encode p) (encode q))
            simp only [encode, tagged] at hf
            omega
          have hq : encode q < fuel := by
            have := Nat.right_le_pair (encode p) (encode q)
            have := Nat.right_le_pair 4 (Nat.pair (encode p) (encode q))
            simp only [encode, tagged] at hf
            omega
          simp [encode, tagged, decodeFuel, Nat.unpair_pair, ihp fuel hp, ihq fuel hq]
  | mu p ih =>
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hp : encode p < fuel := by
            have := Nat.right_le_pair 5 (encode p)
            simp only [encode, tagged] at hf
            omega
          simp [encode, tagged, decodeFuel, Nat.unpair_pair, ih fuel hp]

theorem oracleDecoderComplete : OracleDecoderComplete := fun p => fuel_complete p _ (Nat.lt_succ_self _)

private theorem fuel_sound (fuel : Nat) : ∀ i p, decodeFuel fuel i = some p → encode p = i := by
  induction fuel with
  | zero => intro i p h; simp [decodeFuel] at h
  | succ fuel ih =>
      intro i p h
      cases i with
      | zero => simp [decodeFuel] at h
      | succ k =>
          have hk := Nat.pair_unpair k
          rcases ht : k.unpair.1 with (_ | _ | _ | _ | _ | _ | tag)
          · simp only [decodeFuel, ht, Option.some.injEq] at h
            subst p
            simpa [encode, tagged, ht, Denumerable.encode_ofNat] using congrArg Nat.succ hk
          · by_cases hz : k.unpair.2 = 0
            · simp [decodeFuel, ht, hz] at h
              subst p
              simpa [encode, tagged, ht, hz] using congrArg Nat.succ hk
            · simp [decodeFuel, ht, hz] at h
          · simp only [decodeFuel, ht] at h
            change (decodeFuel fuel k.unpair.2.unpair.1).bind (fun a =>
              (decodeFuel fuel k.unpair.2.unpair.2).bind (fun b => some (Program.pair a b))) = some p at h
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
            obtain ⟨a, ha, b, hb, rfl⟩ := h
            simpa [encode, tagged, ih _ _ ha, ih _ _ hb, Nat.pair_unpair, ht] using congrArg Nat.succ hk
          · simp only [decodeFuel, ht] at h
            change (decodeFuel fuel k.unpair.2.unpair.1).bind (fun a =>
              (decodeFuel fuel k.unpair.2.unpair.2).bind (fun b => some (Program.comp a b))) = some p at h
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
            obtain ⟨a, ha, b, hb, rfl⟩ := h
            simpa [encode, tagged, ih _ _ ha, ih _ _ hb, Nat.pair_unpair, ht] using congrArg Nat.succ hk
          · simp only [decodeFuel, ht] at h
            change (decodeFuel fuel k.unpair.2.unpair.1).bind (fun a =>
              (decodeFuel fuel k.unpair.2.unpair.2).bind (fun b => some (Program.prec a b))) = some p at h
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
            obtain ⟨a, ha, b, hb, rfl⟩ := h
            simpa [encode, tagged, ih _ _ ha, ih _ _ hb, Nat.pair_unpair, ht] using congrArg Nat.succ hk
          · simp only [decodeFuel, ht, Option.map_eq_some_iff] at h
            obtain ⟨a, ha, rfl⟩ := h
            simpa [encode, tagged, ih _ _ ha, ht] using congrArg Nat.succ hk
          · simp [decodeFuel, ht] at h

theorem oracleDecoderSound : OracleDecoderSound := fun i p h => fuel_sound (i + 1) i p h

private theorem fuel_eq_decode (fuel i : Nat) (hi : i < fuel) : decodeFuel fuel i = decode i := by
  cases h : decodeFuel fuel i with
  | some p =>
      have he := fuel_sound fuel i p h
      rw [← he, oracleDecoderComplete]
  | none =>
      cases hd : decode i with
      | none => rfl
      | some p =>
          have he := oracleDecoderSound i p hd
          have hc := fuel_complete p fuel (by simpa [he] using hi)
          rw [he, h] at hc
          contradiction

private theorem getD_previous (i n : Nat) (hi : i < n) :
    ((List.range n).map validIndex).getD i false = validIndex i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

private theorem valid_recurrence (n : Nat) :
    validationStep ((List.range n).map validIndex) = validIndex n := by
  cases n with
  | zero => rfl
  | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) hp
      change validationStep ((List.range (k + 1)).map validIndex) = (decodeFuel (k + 2) (k + 1)).isSome
      simp only [validationStep, List.length_map, List.length_range]
      rw [decodeFuel]
      rcases ht : k.unpair.1 with (_ | _ | _ | _ | _ | _ | tag) <;>
        simp only [ht, fuel_eq_decode _ _ hp, fuel_eq_decode _ _ hl, fuel_eq_decode _ _ hr,
          getD_previous _ _ hp, getD_previous _ _ hl, getD_previous _ _ hr]
      · rfl
      · by_cases hz : k.unpair.2 = 0 <;> simp [hz]
      · simp only [validIndex]
        cases decode k.unpair.2.unpair.1 <;> cases decode k.unpair.2.unpair.2 <;> rfl
      · simp only [validIndex]
        cases decode k.unpair.2.unpair.1 <;> cases decode k.unpair.2.unpair.2 <;> rfl
      · simp only [validIndex]
        cases decode k.unpair.2.unpair.1 <;> cases decode k.unpair.2.unpair.2 <;> rfl
      · simp only [validIndex]
        cases decode k.unpair.2 <;> rfl
      · rfl

private theorem pr_validationStep : Primrec validationStep := by
  have hl : Primrec (fun xs : List Bool => xs.length) := Primrec.list_length
  have hk : Primrec (fun xs : List Bool => xs.length - 1) :=
    Primrec.nat_sub.comp hl (Primrec.const 1)
  have ht : Primrec (fun xs : List Bool => (xs.length - 1).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp : Primrec (fun xs : List Bool => (xs.length - 1).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hk)
  have hleft := (Primrec.list_getD false).comp Primrec.id (Primrec.fst.comp (Primrec.unpair.comp hp))
  have hright := (Primrec.list_getD false).comp Primrec.id (Primrec.snd.comp (Primrec.unpair.comp hp))
  have hb := Primrec.and.comp hleft hright
  have hu := (Primrec.list_getD false).comp Primrec.id hp
  have h : Primrec (fun xs : List Bool =>
      if xs.length = 0 then false else
      if (xs.length - 1).unpair.1 = 0 then true else
      if (xs.length - 1).unpair.1 = 1 then decide ((xs.length - 1).unpair.2 = 0) else
      if (xs.length - 1).unpair.1 = 2 then xs.getD (xs.length - 1).unpair.2.unpair.1 false && xs.getD (xs.length - 1).unpair.2.unpair.2 false else
      if (xs.length - 1).unpair.1 = 3 then xs.getD (xs.length - 1).unpair.2.unpair.1 false && xs.getD (xs.length - 1).unpair.2.unpair.2 false else
      if (xs.length - 1).unpair.1 = 4 then xs.getD (xs.length - 1).unpair.2.unpair.1 false && xs.getD (xs.length - 1).unpair.2.unpair.2 false else
      if (xs.length - 1).unpair.1 = 5 then xs.getD (xs.length - 1).unpair.2 false else false) :=
    Primrec.ite (Primrec.eq.comp hl (Primrec.const 0)) (Primrec.const false)
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (Primrec.const true)
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) (Primrec.eq.comp hp (Primrec.const 0)).decide
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) hb
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) hb
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) hb
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 5)) hu (Primrec.const false)))))))
  apply h.of_eq
  intro xs
  cases hn : xs.length with
  | zero => simp [validationStep, hn]
  | succ k =>
      rcases ht : k.unpair.1 with (_ | _ | _ | _ | _ | _ | tag) <;>
        simp [validationStep, hn, ht]

theorem primitiveRecursiveValidity : PrimitiveRecursiveValidity := by
  have h : Primrec₂ (fun (_ : Unit) n => validIndex n) :=
    Primrec.nat_strong_rec (fun (_ : Unit) n => validIndex n)
      (Primrec.option_some.comp (pr_validationStep.comp Primrec.snd)).to₂
      (fun _ n => congrArg Option.some (valid_recurrence n))
  exact h.comp (Primrec.const ()) Primrec.id

theorem primitiveRecursiveEncodedDecoder : PrimitiveRecursiveEncodedDecoder := by
  have h := Primrec.ite (Primrec.eq.comp primitiveRecursiveValidity (Primrec.const true))
    (Primrec.option_some.comp Primrec.id) (Primrec.const (none : Option Nat))
  apply h.of_eq
  intro i
  cases hd : decode i with
  | none => simp [encodedDecode, validIndex, hd]
  | some p => simp [encodedDecode, validIndex, hd, oracleDecoderSound i p hd]

end LogicLineages.ComputabilityKnowledge.OracleDecoderProof
