module
public import LogicLineages.OrdinalComparison.RawNormCodeTargets
public import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem rawNormTableEquation : Targets.RawNormTableEquation :=
  ⟨rfl, fun _ => rfl⟩

private theorem rawNormTable_length (n : Nat) : (rawNormTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rawNormTable, List.length_append, List.length_singleton, ih]

private theorem decoded_norm_succ (n : Nat) :
    Vendor.R1.treeWeight (rawNoteDecode (n + 1)) =
      (n.unpair.2.unpair.1 + 1) * (1 + Vendor.R1.treeWeight (rawNoteDecode n.unpair.1)) +
        Vendor.R1.treeWeight (rawNoteDecode n.unpair.2.unpair.2) := by
  rw [rawNoteDecode]
  rfl

private theorem rawNormTable_correct (n : Nat) :
    ∀ i : Nat, i ≤ n → (rawNormTable n).getD i 0 = Vendor.R1.treeWeight (rawNoteDecode i) := by
  induction n with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      rw [rawNoteDecode]
      rfl
  | succ n ih =>
      intro i hi
      by_cases hin : i ≤ n
      · rw [rawNormTable, List.getD_append _ _ _ _ (by rw [rawNormTable_length]; omega)]
        exact ih i hin
      · have hieq : i = n + 1 := by omega
        subst i
        rw [rawNormTable, List.getD_append_right _ _ _ _ (by rw [rawNormTable_length])]
        simp only [rawNormTable_length, Nat.sub_self, List.getD_cons_zero]
        rw [ih n.unpair.1 (Nat.unpair_left_le n),
          ih n.unpair.2.unpair.2 ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n)),
          decoded_norm_succ]

private theorem rawNormCode_decodeCorrect (n : Nat) :
    rawNormCode n = Vendor.R1.treeWeight (rawNoteDecode n) :=
  rawNormTable_correct n n le_rfl

theorem rawNormCodeEquation : Targets.RawNormCodeEquation := by
  constructor
  · rfl
  · intro n
    rw [rawNormCode_decodeCorrect, decoded_norm_succ,
      rawNormCode_decodeCorrect, rawNormCode_decodeCorrect]

theorem rawNormCodeCorrect : Targets.RawNormCodeCorrect := by
  intro a
  rw [rawNormCode_decodeCorrect, rawNoteDecodeEncode a]

theorem rawNormCodePrimitiveRecursive : Targets.RawNormCodePrimitiveRecursive := by
  let step : Nat → List Nat → List Nat := fun n table =>
    table ++ [(n.unpair.2.unpair.1 + 1) * (1 + table.getD n.unpair.1 0) +
      table.getD n.unpair.2.unpair.2 0]
  have hleft : Primrec (fun p : Nat × List Nat => p.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hrest : Primrec (fun p : Nat × List Nat => p.1.unpair.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
  have hcoeff : Primrec (fun p : Nat × List Nat => p.1.unpair.2.unpair.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp hrest)
  have hright : Primrec (fun p : Nat × List Nat => p.1.unpair.2.unpair.2) :=
    Primrec.snd.comp hrest
  have hlookupL := (Primrec.list_getD 0).comp Primrec.snd hleft
  have hlookupR := (Primrec.list_getD 0).comp Primrec.snd hright
  have hval := Primrec.nat_add.comp
    (Primrec.nat_mul.comp hcoeff (Primrec.nat_add.comp (Primrec.const 1) hlookupL)) hlookupR
  have hstep : Primrec₂ step := Primrec.list_concat.comp Primrec.snd hval
  have htable : Primrec rawNormTable := (Primrec.nat_rec₁ [0] hstep).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change step n (Nat.rec [0] step n) = _
        rw [ih]
        rfl)
  apply Primrec.nat_iff.mp
  exact (Primrec.list_getD 0).comp htable Primrec.id

end LogicLineages.OrdinalComparison
