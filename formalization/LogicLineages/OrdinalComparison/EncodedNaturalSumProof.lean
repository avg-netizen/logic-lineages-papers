module
public import LogicLineages.OrdinalComparison.EncodedNaturalSumTargets
public import LogicLineages.OrdinalComparison.RawComparisonProof
public import LogicLineages.OrdinalComparison.NaturalSumInterpretation
public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace LogicLineages.OrdinalComparison

private def sourceNaturalSumCode (n : Nat) : Nat :=
  rawNoteEncode (rawNaturalSum (rawNoteDecode n.unpair.1) (rawNoteDecode n.unpair.2))

private theorem rawNaturalSum_zero_right (a : ONote) : rawNaturalSum a 0 = a := by
  cases a <;> rw [rawNaturalSum.eq_def] <;> rfl

private theorem rawNaturalSum_zero_left (a : ONote) : rawNaturalSum 0 a = a := by
  cases a <;> rw [rawNaturalSum.eq_def] <;> rfl

private theorem encodedNaturalSumStep_correct (n : Nat) (table : List Nat)
    (h : ∀ i : Nat, i < n → table.getD i 0 = sourceNaturalSumCode i) :
    encodedNaturalSumStep n table = sourceNaturalSumCode n := by
  simp only [sourceNaturalSumCode] at h ⊢
  generalize ha : n.unpair.1 = a
  generalize hb : n.unpair.2 = b
  have hab : Nat.pair a b = n := by rw [← ha, ← hb, Nat.pair_unpair]
  cases a with
  | zero =>
      simp [encodedNaturalSumStep, ha, hb, (rawNoteDecodeEquation).1, rawNaturalSum_zero_left,
        rawNoteEncodeDecode b]
  | succ a =>
      cases b with
      | zero =>
          simp [encodedNaturalSumStep, ha, hb, (rawNoteDecodeEquation).1,
            rawNaturalSum_zero_right, rawNoteEncodeDecode (a + 1)]
      | succ b =>
          have htA : a.unpair.2.unpair.2 < a + 1 :=
            Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le a))
          have htB : b.unpair.2.unpair.2 < b + 1 :=
            Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le b))
          have hL := h (Nat.pair (a + 1) b.unpair.2.unpair.2) (by
            rw [← hab]
            exact Nat.pair_lt_pair_right _ htB)
          have hE := h (Nat.pair a.unpair.2.unpair.2 b.unpair.2.unpair.2) (by
            rw [← hab]
            exact (Nat.pair_lt_pair_left _ htA).trans (Nat.pair_lt_pair_right _ htB))
          have hG := h (Nat.pair a.unpair.2.unpair.2 (b + 1)) (by
            rw [← hab]
            exact Nat.pair_lt_pair_left _ htA)
          simp only [Nat.unpair_pair] at hL hE hG
          simp only [encodedNaturalSumStep, ha, hb, Nat.succ_ne_zero, ↓reduceIte, Nat.pred_succ]
          rw [rawComparisonCode_decodeCorrect, (rawNoteDecodeEquation).2 a,
            (rawNoteDecodeEquation).2 b]
          cases hc : ONote.cmp (rawNoteDecode a.unpair.1) (rawNoteDecode b.unpair.1) with
          | lt =>
              simp only [hc, orderingCode, ↓reduceIte]
              rw [hL]
              simp [rawNaturalSum, hc, encodedNodeCode, rawNoteEncode,
                (rawNoteDecodeEquation).2 a, rawNoteEncodeDecode b.unpair.1]
          | eq =>
              simp only [hc, orderingCode, Nat.one_ne_zero, ↓reduceIte]
              rw [hE]
              have hcoef : (a.unpair.2.unpair.1 + 1) + (b.unpair.2.unpair.1 + 1) - 1 =
                  a.unpair.2.unpair.1 + b.unpair.2.unpair.1 + 1 := by omega
              simp [rawNaturalSum, hc, encodedNodeCode, rawNoteEncode,
                rawNoteEncodeDecode a.unpair.1, PNat.add_coe, hcoef]
          | gt =>
              simp only [hc, orderingCode, ↓reduceIte]
              rw [hG]
              simp [rawNaturalSum, hc, encodedNodeCode, rawNoteEncode,
                (rawNoteDecodeEquation).2 b, rawNoteEncodeDecode a.unpair.1]

private theorem encodedNaturalSumTable_length (n : Nat) :
    (encodedNaturalSumTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodedNaturalSumTable, List.length_append, List.length_singleton, ih]

private theorem encodedNaturalSumTable_correct (n : Nat) :
    ∀ i : Nat, i ≤ n → (encodedNaturalSumTable n).getD i 0 = sourceNaturalSumCode i := by
  induction n with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [encodedNaturalSumTable, sourceNaturalSumCode, rawNoteDecode, rawNaturalSum_zero_left, rawNoteEncode]
  | succ n ih =>
      intro i hi
      by_cases hin : i ≤ n
      · rw [encodedNaturalSumTable, List.getD_append _ _ _ _ (by rw [encodedNaturalSumTable_length]; omega)]
        exact ih i hin
      · have heq : i = n + 1 := by omega
        subst i
        rw [encodedNaturalSumTable, List.getD_append_right _ _ _ _ (by rw [encodedNaturalSumTable_length])]
        simp only [encodedNaturalSumTable_length, Nat.sub_self, List.getD_cons_zero]
        exact encodedNaturalSumStep_correct _ _ (fun j hj => ih j (by omega))

theorem encodedNaturalSumCorrect : Targets.EncodedNaturalSumCorrect := by
  intro a b
  have h := encodedNaturalSumTable_correct (Nat.pair (rawNoteEncode a) (rawNoteEncode b))
    (Nat.pair (rawNoteEncode a) (rawNoteEncode b)) le_rfl
  simpa only [encodedNaturalSum, sourceNaturalSumCode, Nat.unpair_pair,
    rawNoteDecodeEncode a, rawNoteDecodeEncode b] using h

theorem encodedNodeCode_primrec {α : Type} [Primcodable α] {e c t : α → Nat}
    (he : Primrec e) (hc : Primrec c) (ht : Primrec t) :
    Primrec (fun x => encodedNodeCode (e x) (c x) (t x)) :=
  Primrec.succ.comp (Primrec₂.natPair.comp he (Primrec₂.natPair.comp hc ht))

private theorem encodedNaturalSumStep_primrec : Primrec₂ encodedNaturalSumStep := by
  have ha : Primrec (fun p : Nat × List Nat => p.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hb : Primrec (fun p : Nat × List Nat => p.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hl := Primrec.unpair.comp (Primrec.nat_sub.comp ha (Primrec.const 1))
  have hr := Primrec.unpair.comp (Primrec.nat_sub.comp hb (Primrec.const 1))
  have he := Primrec.fst.comp hl
  have hf := Primrec.fst.comp hr
  have hc := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hl))
  have hd := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hr))
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hl))
  have hu := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hr))
  have hL := (Primrec.list_getD 0).comp Primrec.snd (Primrec₂.natPair.comp ha hu)
  have hE := (Primrec.list_getD 0).comp Primrec.snd (Primrec₂.natPair.comp ht hu)
  have hG := (Primrec.list_getD 0).comp Primrec.snd (Primrec₂.natPair.comp ht hb)
  have hcmp : Primrec₂ rawComparisonCode := rawComparisonPrimitiveRecursive
  have horder := hcmp.comp he hf
  have hsum := Primrec.succ.comp (Primrec.nat_add.comp hc hd)
  exact Primrec.ite (Primrec.eq.comp ha (Primrec.const 0)) hb
    (Primrec.ite (Primrec.eq.comp hb (Primrec.const 0)) ha
      (Primrec.ite (Primrec.eq.comp horder (Primrec.const 0)) (encodedNodeCode_primrec hf hd hL)
        (Primrec.ite (Primrec.eq.comp horder (Primrec.const 1)) (encodedNodeCode_primrec he hsum hE)
          (encodedNodeCode_primrec he hc hG))))

theorem encodedNaturalSumPrimitiveRecursive : Targets.EncodedNaturalSumPrimitiveRecursive := by
  let step : Nat → List Nat → List Nat := fun n table =>
    table ++ [encodedNaturalSumStep (n + 1) table]
  have hs : Primrec₂ step := Primrec.list_concat.comp Primrec.snd
    (encodedNaturalSumStep_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  have htable : Primrec encodedNaturalSumTable := (Primrec.nat_rec₁ [0] hs).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change step n (Nat.rec [0] step n) = _
        rw [ih]
        rfl)
  exact (Primrec.list_getD 0).comp (htable.comp Primrec₂.natPair) Primrec₂.natPair

theorem encodedNaturalSumSourceCorrect : Targets.EncodedNaturalSumSourceCorrect := by
  intro a b
  rw [encodedNaturalSumCorrect a.1 b.1, rawNoteDecodeEncode (rawNaturalSum a.1 b.1)]
  exact ⟨rawNaturalSum_normal a.1 b.1 a.2 b.2, naturalSumDenotation a b, rawNaturalSum_norm a.1 b.1⟩

end LogicLineages.OrdinalComparison
