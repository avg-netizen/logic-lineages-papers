module
public import LogicLineages.OrdinalComparison.EncodedNaturalProductTargets
public import LogicLineages.OrdinalComparison.EncodedNaturalSumProof
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem sum_decode_correct (a b : Nat) :
    encodedNaturalSum a b = rawNoteEncode (rawNaturalSum (rawNoteDecode a) (rawNoteDecode b)) := by
  have h := encodedNaturalSumCorrect (rawNoteDecode a) (rawNoteDecode b)
  rwa [rawNoteEncodeDecode a, rawNoteEncodeDecode b] at h

private def sourceMonomialProductCode (n : Nat) : Nat :=
  rawNoteEncode (rawMonomialProduct (rawNoteDecode n.unpair.1.unpair.1)
    ⟨n.unpair.1.unpair.2 + 1, Nat.succ_pos _⟩ (rawNoteDecode n.unpair.2))

private theorem encodedMonomialProductStep_correct (n : Nat) (table : List Nat)
    (h : ∀ i : Nat, i < n → table.getD i 0 = sourceMonomialProductCode i) :
    encodedMonomialProductStep n table = sourceMonomialProductCode n := by
  simp only [sourceMonomialProductCode] at h ⊢
  let p := n.unpair.1
  have hp : n.unpair.1 = p := rfl
  generalize hb : n.unpair.2 = b
  have hpb : Nat.pair p b = n := by rw [← hp, ← hb, Nat.pair_unpair]
  cases b with
  | zero =>
      simp [encodedMonomialProductStep, hp, hb, (rawNoteDecodeEquation).1,
        rawMonomialProduct, rawNoteEncode]
  | succ b =>
      have htail := h (Nat.pair p b.unpair.2.unpair.2) (by
        rw [← hpb]
        exact Nat.pair_lt_pair_right p
          (Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le b))))
      simp only [Nat.unpair_pair] at htail
      simp only [encodedMonomialProductStep, hp, hb, Nat.succ_ne_zero, ↓reduceIte, Nat.pred_succ]
      rw [htail, (rawNoteDecodeEquation).2 b]
      simp only [rawMonomialProduct]
      have hnode : encodedNodeCode (encodedNaturalSum p.unpair.1 b.unpair.1)
          ((p.unpair.2 + 1) * (b.unpair.2.unpair.1 + 1) - 1) 0 =
          rawNoteEncode (.oadd (rawNaturalSum (rawNoteDecode p.unpair.1) (rawNoteDecode b.unpair.1))
            ⟨(p.unpair.2 + 1) * (b.unpair.2.unpair.1 + 1),
              Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)⟩ 0) := by
        rw [sum_decode_correct]
        rfl
      rw [hnode, encodedNaturalSumCorrect]
      rfl

private theorem encodedMonomialProductTable_length (n : Nat) :
    (encodedMonomialProductTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodedMonomialProductTable, List.length_append, List.length_singleton, ih]

private theorem encodedMonomialProductTable_correct (n : Nat) :
    ∀ i : Nat, i ≤ n → (encodedMonomialProductTable n).getD i 0 = sourceMonomialProductCode i := by
  induction n with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [encodedMonomialProductTable, sourceMonomialProductCode, rawNoteDecode,
        rawMonomialProduct, rawNoteEncode]
  | succ n ih =>
      intro i hi
      by_cases hin : i ≤ n
      · rw [encodedMonomialProductTable,
          List.getD_append _ _ _ _ (by rw [encodedMonomialProductTable_length]; omega)]
        exact ih i hin
      · have heq : i = n + 1 := by omega
        subst i
        rw [encodedMonomialProductTable,
          List.getD_append_right _ _ _ _ (by rw [encodedMonomialProductTable_length])]
        simp only [encodedMonomialProductTable_length, Nat.sub_self, List.getD_cons_zero]
        exact encodedMonomialProductStep_correct _ _ (fun j hj => ih j (by omega))

theorem encodedMonomialProductCorrect : Targets.EncodedMonomialProductCorrect := by
  intro e b c
  let n := Nat.pair (Nat.pair (rawNoteEncode e) ((c : Nat) - 1)) (rawNoteEncode b)
  have h := encodedMonomialProductTable_correct n n le_rfl
  have hc : (⟨(c : Nat) - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = c :=
    Subtype.ext (Nat.sub_add_cancel c.pos)
  simpa only [encodedMonomialProduct, n, sourceMonomialProductCode, Nat.unpair_pair,
    rawNoteDecodeEncode e, rawNoteDecodeEncode b, hc] using h

private theorem monomial_decode_correct (e c b : Nat) :
    encodedMonomialProduct e c b = rawNoteEncode
      (rawMonomialProduct (rawNoteDecode e) ⟨c + 1, Nat.succ_pos c⟩ (rawNoteDecode b)) := by
  have h := encodedMonomialProductCorrect (rawNoteDecode e) (rawNoteDecode b) ⟨c + 1, Nat.succ_pos c⟩
  simpa [rawNoteEncodeDecode e, rawNoteEncodeDecode b] using h

private theorem encodedMonomialProductStep_primrec : Primrec₂ encodedMonomialProductStep := by
  have hp : Primrec (fun p : Nat × List Nat => p.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hb : Primrec (fun p : Nat × List Nat => p.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have he := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hc := Primrec.snd.comp (Primrec.unpair.comp hp)
  have hf := Primrec.unpair.comp (Primrec.nat_sub.comp hb (Primrec.const 1))
  have hd := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hf))
  have hu := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hf))
  have hsum : Primrec₂ encodedNaturalSum := encodedNaturalSumPrimitiveRecursive
  have hexp := hsum.comp he (Primrec.fst.comp hf)
  have hcoef := Primrec.nat_sub.comp
    (Primrec.nat_mul.comp (Primrec.succ.comp hc) (Primrec.succ.comp hd)) (Primrec.const 1)
  have hnode := encodedNodeCode_primrec hexp hcoef (Primrec.const 0)
  have htail := (Primrec.list_getD 0).comp Primrec.snd (Primrec₂.natPair.comp hp hu)
  exact Primrec.ite (Primrec.eq.comp hb (Primrec.const 0)) (Primrec.const 0) (hsum.comp hnode htail)

theorem encodedMonomialProductPrimitiveRecursive : Targets.EncodedMonomialProductPrimitiveRecursive := by
  let step : Nat → List Nat → List Nat := fun n table =>
    table ++ [encodedMonomialProductStep (n + 1) table]
  have hs : Primrec₂ step := Primrec.list_concat.comp Primrec.snd
    (encodedMonomialProductStep_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  have htable : Primrec encodedMonomialProductTable := (Primrec.nat_rec₁ [0] hs).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change step n (Nat.rec [0] step n) = _
        rw [ih]
        rfl)
  have hindex : Primrec (fun p : (Nat × Nat) × Nat => Nat.pair (Nat.pair p.1.1 p.1.2) p.2) :=
    Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) Primrec.snd
  exact (Primrec.list_getD 0).comp (htable.comp hindex) hindex

private def sourceNaturalProductCode (n : Nat) : Nat :=
  rawNoteEncode (rawNaturalProduct (rawNoteDecode n.unpair.1) (rawNoteDecode n.unpair.2))

private theorem encodedNaturalProductStep_correct (n : Nat) (table : List Nat)
    (h : ∀ i : Nat, i < n → table.getD i 0 = sourceNaturalProductCode i) :
    encodedNaturalProductStep n table = sourceNaturalProductCode n := by
  simp only [sourceNaturalProductCode] at h ⊢
  generalize ha : n.unpair.1 = a
  generalize hb : n.unpair.2 = b
  have hab : Nat.pair a b = n := by rw [← ha, ← hb, Nat.pair_unpair]
  cases a with
  | zero =>
      simp [encodedNaturalProductStep, ha, hb, (rawNoteDecodeEquation).1, rawNaturalProduct, rawNoteEncode]
  | succ a =>
      have htail := h (Nat.pair a.unpair.2.unpair.2 b) (by
        rw [← hab]
        exact Nat.pair_lt_pair_left b
          (Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le a))))
      simp only [Nat.unpair_pair] at htail
      simp only [encodedNaturalProductStep, ha, hb, Nat.succ_ne_zero, ↓reduceIte, Nat.pred_succ]
      rw [htail, monomial_decode_correct, encodedNaturalSumCorrect, (rawNoteDecodeEquation).2 a]
      rfl

private theorem encodedNaturalProductTable_length (n : Nat) :
    (encodedNaturalProductTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodedNaturalProductTable, List.length_append, List.length_singleton, ih]

private theorem encodedNaturalProductTable_correct (n : Nat) :
    ∀ i : Nat, i ≤ n → (encodedNaturalProductTable n).getD i 0 = sourceNaturalProductCode i := by
  induction n with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [encodedNaturalProductTable, sourceNaturalProductCode, rawNoteDecode, rawNaturalProduct, rawNoteEncode]
  | succ n ih =>
      intro i hi
      by_cases hin : i ≤ n
      · rw [encodedNaturalProductTable,
          List.getD_append _ _ _ _ (by rw [encodedNaturalProductTable_length]; omega)]
        exact ih i hin
      · have heq : i = n + 1 := by omega
        subst i
        rw [encodedNaturalProductTable,
          List.getD_append_right _ _ _ _ (by rw [encodedNaturalProductTable_length])]
        simp only [encodedNaturalProductTable_length, Nat.sub_self, List.getD_cons_zero]
        exact encodedNaturalProductStep_correct _ _ (fun j hj => ih j (by omega))

theorem encodedNaturalProductCorrect : Targets.EncodedNaturalProductCorrect := by
  intro a b
  have h := encodedNaturalProductTable_correct (Nat.pair (rawNoteEncode a) (rawNoteEncode b))
    (Nat.pair (rawNoteEncode a) (rawNoteEncode b)) le_rfl
  simpa only [encodedNaturalProduct, sourceNaturalProductCode, Nat.unpair_pair,
    rawNoteDecodeEncode a, rawNoteDecodeEncode b] using h

private theorem encodedNaturalProductStep_primrec : Primrec₂ encodedNaturalProductStep := by
  have ha : Primrec (fun p : Nat × List Nat => p.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hb : Primrec (fun p : Nat × List Nat => p.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hf := Primrec.unpair.comp (Primrec.nat_sub.comp ha (Primrec.const 1))
  have he := Primrec.fst.comp hf
  have hc := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hf))
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hf))
  have hmono : Primrec (fun p : (Nat × Nat) × Nat => encodedMonomialProduct p.1.1 p.1.2 p.2) :=
    encodedMonomialProductPrimitiveRecursive
  have hm := hmono.comp ((he.pair hc).pair hb)
  have htail := (Primrec.list_getD 0).comp Primrec.snd (Primrec₂.natPair.comp ht hb)
  have hsum : Primrec₂ encodedNaturalSum := encodedNaturalSumPrimitiveRecursive
  exact Primrec.ite (Primrec.eq.comp ha (Primrec.const 0)) (Primrec.const 0) (hsum.comp hm htail)

theorem encodedNaturalProductPrimitiveRecursive : Targets.EncodedNaturalProductPrimitiveRecursive := by
  let step : Nat → List Nat → List Nat := fun n table =>
    table ++ [encodedNaturalProductStep (n + 1) table]
  have hs : Primrec₂ step := Primrec.list_concat.comp Primrec.snd
    (encodedNaturalProductStep_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  have htable : Primrec encodedNaturalProductTable := (Primrec.nat_rec₁ [0] hs).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change step n (Nat.rec [0] step n) = _
        rw [ih]
        rfl)
  exact (Primrec.list_getD 0).comp (htable.comp Primrec₂.natPair) Primrec₂.natPair

theorem encodedNaturalProductSourceCorrect : Targets.EncodedNaturalProductSourceCorrect := by
  intro a b
  rw [encodedNaturalProductCorrect a.1 b.1, rawNoteDecodeEncode (rawNaturalProduct a.1 b.1)]
  exact ⟨rawNaturalProduct_normal a.1 a.2 b.1 b.2, naturalProductDenotation a b,
    rawNaturalProduct_norm a.1 b.1⟩

end LogicLineages.OrdinalComparison
