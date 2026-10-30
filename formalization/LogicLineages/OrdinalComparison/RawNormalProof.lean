module
public import LogicLineages.OrdinalComparison.RawNormalTargets
public import LogicLineages.OrdinalComparison.RawComparisonProof
public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem nf_oadd_iff (e : ONote) (c : ℕ+) (t : ONote) :
    ONote.NF (.oadd e c t) ↔ ONote.NF e ∧ ONote.NF t ∧ ONote.TopBelow e t := by
  constructor
  · intro hn
    exact ⟨hn.fst, hn.snd, ((@ONote.nfBelow_iff_topBelow e hn.fst t).mp hn.snd').2⟩
  · rintro ⟨he, ht, htop⟩
    exact ONote.NF.oadd he c ((@ONote.nfBelow_iff_topBelow e he t).mpr ⟨ht, htop⟩)

private theorem topBelow_decoded (e t : Nat) :
    (t = 0 ∨ rawComparisonCode t.pred.unpair.1 e = 0) ↔
      ONote.TopBelow (rawNoteDecode e) (rawNoteDecode t) := by
  cases t with
  | zero => simp [rawNoteDecode, ONote.TopBelow]
  | succ t =>
      simp only [Nat.succ_ne_zero, false_or, Nat.pred_succ]
      rw [rawComparisonCode_decodeCorrect, (rawNoteDecodeEquation).2 t]
      simp only [ONote.TopBelow]
      cases ONote.cmp (rawNoteDecode t.unpair.1) (rawNoteDecode e) <;> simp [orderingCode]

private theorem rawNormalStep_correct (n : Nat) (table : List Nat)
    (h : ∀ i : Nat, i < n → (table.getD i 0 = 1 ↔ ONote.NF (rawNoteDecode i))) :
    rawNormalStep n table = 1 ↔ ONote.NF (rawNoteDecode n) := by
  cases n with
  | zero => simp [rawNormalStep, rawNoteDecode, ONote.NF.zero]
  | succ n =>
      have he := h n.unpair.1 (Nat.lt_succ_of_le (Nat.unpair_left_le n))
      have ht := h n.unpair.2.unpair.2
        (Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n)))
      have htest := and_congr he (and_congr ht (topBelow_decoded n.unpair.1 n.unpair.2.unpair.2))
      simp only [rawNormalStep, Nat.succ_ne_zero, ↓reduceIte, Nat.pred_succ]
      rw [(rawNoteDecodeEquation).2 n, nf_oadd_iff, ← htest]
      split_ifs <;> simp_all

private theorem rawNormalTable_length (n : Nat) : (rawNormalTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rawNormalTable, List.length_append, List.length_singleton, ih]

private theorem rawNormalTable_correct (n : Nat) :
    ∀ i : Nat, i ≤ n → ((rawNormalTable n).getD i 0 = 1 ↔ ONote.NF (rawNoteDecode i)) := by
  induction n with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [rawNormalTable, rawNoteDecode, ONote.NF.zero]
  | succ n ih =>
      intro i hi
      by_cases hin : i ≤ n
      · rw [rawNormalTable, List.getD_append _ _ _ _ (by rw [rawNormalTable_length]; omega)]
        exact ih i hin
      · have hieq : i = n + 1 := by omega
        subst i
        rw [rawNormalTable, List.getD_append_right _ _ _ _ (by rw [rawNormalTable_length])]
        simp only [rawNormalTable_length, Nat.sub_self, List.getD_cons_zero]
        apply rawNormalStep_correct
        intro j hj
        exact ih j (by omega)

theorem rawNormalDecodeCorrect : Targets.RawNormalDecodeCorrect :=
  fun n => rawNormalTable_correct n n le_rfl

theorem rawNormalCorrect : Targets.RawNormalCorrect := by
  intro a
  rw [rawNormalDecodeCorrect, rawNoteDecodeEncode]

private theorem rawNormalStep_primrec : Primrec₂ rawNormalStep := by
  have hfields := Primrec.unpair.comp (Primrec.nat_sub.comp (Primrec.fst : Primrec (fun p : Nat × List Nat => p.1)) (Primrec.const 1))
  have he := Primrec.fst.comp hfields
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hfields))
  have hgetE := (Primrec.list_getD 0).comp Primrec.snd he
  have hgetT := (Primrec.list_getD 0).comp Primrec.snd ht
  have hcmp : Primrec₂ rawComparisonCode := rawComparisonPrimitiveRecursive
  have hcompare := hcmp.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp ht (Primrec.const 1)))) he
  have htop := (Primrec.eq.comp ht (Primrec.const 0)).or
    (Primrec.eq.comp hcompare (Primrec.const 0))
  have htest := (Primrec.eq.comp hgetE (Primrec.const 1)).and
    ((Primrec.eq.comp hgetT (Primrec.const 1)).and htop)
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 1)
    (Primrec.ite htest (Primrec.const 1) (Primrec.const 0))

theorem rawNormalPrimitiveRecursive : Targets.RawNormalPrimitiveRecursive := by
  let step : Nat → List Nat → List Nat := fun n table =>
    table ++ [rawNormalStep (n + 1) table]
  have hstep : Primrec₂ step := Primrec.list_concat.comp Primrec.snd
    (rawNormalStep_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  have htable : Primrec rawNormalTable := (Primrec.nat_rec₁ [1] hstep).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change step n (Nat.rec [1] step n) = _
        rw [ih]
        rfl)
  apply Primrec.nat_iff.mp
  exact (Primrec.list_getD 0).comp htable Primrec.id

end LogicLineages.OrdinalComparison
