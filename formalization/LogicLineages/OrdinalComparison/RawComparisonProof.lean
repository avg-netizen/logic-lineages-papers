module
public import LogicLineages.OrdinalComparison.RawComparisonTargets
public import LogicLineages.OrdinalComparison.RawNotationCode
public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem orderingCode_then (x y : Ordering) :
    orderingCode (x.then y) = if orderingCode x = 1 then orderingCode y else orderingCode x := by
  cases x <;> rfl

private theorem orderingCode_natCmp (a b : Nat) :
    orderingCode (_root_.cmp a b) = if a < b then 0 else if b < a then 2 else 1 := by
  by_cases hab : a < b
  · rw [(cmp_eq_lt_iff a b).mpr hab]
    simp [orderingCode, hab]
  · by_cases hba : b < a
    · rw [(cmp_eq_gt_iff a b).mpr hba]
      simp [orderingCode, hab, hba]
    · have heq : a = b := Nat.le_antisymm (Nat.le_of_not_gt hba) (Nat.le_of_not_gt hab)
      rw [(cmp_eq_eq_iff a b).mpr heq]
      simp [orderingCode, hab, hba]

private theorem rawComparisonStep_correct (n : Nat) (table : List Nat)
    (h : ∀ i : Nat, i < n →
      table.getD i 1 = orderingCode (ONote.cmp (rawNoteDecode i.unpair.1) (rawNoteDecode i.unpair.2))) :
    rawComparisonStep n table =
      orderingCode (ONote.cmp (rawNoteDecode n.unpair.1) (rawNoteDecode n.unpair.2)) := by
  generalize ha : n.unpair.1 = a
  generalize hb : n.unpair.2 = b
  have hab : Nat.pair a b = n := by rw [← ha, ← hb, Nat.pair_unpair]
  cases a with
  | zero =>
      cases b with
      | zero => simp [rawComparisonStep, ha, hb, rawNoteDecode, ONote.cmp, orderingCode]
      | succ b => simp [rawComparisonStep, ha, hb, rawNoteDecode, ONote.cmp, orderingCode]
  | succ a =>
      cases b with
      | zero => simp [rawComparisonStep, ha, hb, rawNoteDecode, ONote.cmp, orderingCode]
      | succ b =>
          have he : Nat.pair a.unpair.1 b.unpair.1 < n := by
            rw [← hab]
            exact (Nat.pair_lt_pair_left _ (Nat.lt_succ_of_le (Nat.unpair_left_le a))).trans
              (Nat.pair_lt_pair_right _ (Nat.lt_succ_of_le (Nat.unpair_left_le b)))
          have ht : Nat.pair a.unpair.2.unpair.2 b.unpair.2.unpair.2 < n := by
            rw [← hab]
            exact (Nat.pair_lt_pair_left _
              (Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le a)))).trans
              (Nat.pair_lt_pair_right _
                (Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le b))))
          have hexp := h _ he
          have htail := h _ ht
          simp only [Nat.unpair_pair] at hexp htail
          simp only [rawComparisonStep, ha, hb, Nat.succ_ne_zero, ↓reduceIte, Nat.pred_succ]
          rw [hexp, htail]
          rw [rawNoteDecode, rawNoteDecode]
          simp only [ONote.cmp, orderingCode_then]
          rw [orderingCode_natCmp]
          by_cases h₁ : a.unpair.2.unpair.1 < b.unpair.2.unpair.1
          · simp [h₁]
          · by_cases h₂ : b.unpair.2.unpair.1 < a.unpair.2.unpair.1
            · simp [h₁, h₂]
            · simp [h₁, h₂]

private theorem rawComparisonTable_length (n : Nat) :
    (rawComparisonTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rawComparisonTable, List.length_append, List.length_singleton, ih]

private theorem rawComparisonTable_correct (n : Nat) :
    ∀ i : Nat, i ≤ n → (rawComparisonTable n).getD i 1 =
      orderingCode (ONote.cmp (rawNoteDecode i.unpair.1) (rawNoteDecode i.unpair.2)) := by
  induction n with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [rawComparisonTable, rawNoteDecode, ONote.cmp, orderingCode]
  | succ n ih =>
      intro i hi
      by_cases hin : i ≤ n
      · rw [rawComparisonTable, List.getD_append _ _ _ _ (by rw [rawComparisonTable_length]; omega)]
        exact ih i hin
      · have hieq : i = n + 1 := by omega
        subst i
        rw [rawComparisonTable, List.getD_append_right _ _ _ _ (by rw [rawComparisonTable_length])]
        simp only [rawComparisonTable_length, Nat.sub_self, List.getD_cons_zero]
        apply rawComparisonStep_correct
        intro j hj
        exact ih j (by omega)

theorem rawComparisonCode_decodeCorrect (a b : Nat) :
    rawComparisonCode a b = orderingCode (ONote.cmp (rawNoteDecode a) (rawNoteDecode b)) := by
  unfold rawComparisonCode
  simpa only [Nat.unpair_pair] using rawComparisonTable_correct (Nat.pair a b) (Nat.pair a b) le_rfl

theorem rawComparisonCorrect : Targets.RawComparisonCorrect := by
  intro a b
  rw [rawComparisonCode_decodeCorrect, rawNoteDecodeEncode, rawNoteDecodeEncode]

private theorem rawComparisonStep_primrec : Primrec₂ rawComparisonStep := by
  have ha : Primrec (fun p : Nat × List Nat => p.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hb : Primrec (fun p : Nat × List Nat => p.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hl := Primrec.unpair.comp (Primrec.nat_sub.comp ha (Primrec.const 1))
  have hr := Primrec.unpair.comp (Primrec.nat_sub.comp hb (Primrec.const 1))
  have hc₁ := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hl))
  have hc₂ := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hr))
  have heIndex := Primrec₂.natPair.comp (Primrec.fst.comp hl) (Primrec.fst.comp hr)
  have htIndex := Primrec₂.natPair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hl)))
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hr)))
  have he := (Primrec.list_getD 1).comp Primrec.snd heIndex
  have ht := (Primrec.list_getD 1).comp Primrec.snd htIndex
  exact Primrec.ite (Primrec.eq.comp ha (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hb (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hb (Primrec.const 0)) (Primrec.const 2)
      (Primrec.ite (Primrec.eq.comp he (Primrec.const 1))
        (Primrec.ite (Primrec.nat_lt.comp hc₁ hc₂) (Primrec.const 0)
          (Primrec.ite (Primrec.nat_lt.comp hc₂ hc₁) (Primrec.const 2) ht)) he))

theorem rawComparisonPrimitiveRecursive : Targets.RawComparisonPrimitiveRecursive := by
  let step : Nat → List Nat → List Nat := fun n table =>
    table ++ [rawComparisonStep (n + 1) table]
  have hstep : Primrec₂ step := Primrec.list_concat.comp Primrec.snd
    (rawComparisonStep_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  have htable : Primrec rawComparisonTable := (Primrec.nat_rec₁ [1] hstep).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change step n (Nat.rec [1] step n) = _
        rw [ih]
        rfl)
  exact (Primrec.list_getD 1).comp (htable.comp Primrec₂.natPair) Primrec₂.natPair

private theorem orderingCode_zero (o : Ordering) : orderingCode o = 0 ↔ o = .lt := by
  cases o <;> simp [orderingCode]

private theorem orderingCode_one (o : Ordering) : orderingCode o = 1 ↔ o = .eq := by
  cases o <;> simp [orderingCode]

private theorem orderingCode_two (o : Ordering) : orderingCode o = 2 ↔ o = .gt := by
  cases o <;> simp [orderingCode]

theorem rawComparisonOrdinalCorrect : Targets.RawComparisonOrdinalCorrect := by
  intro a b
  rw [rawComparisonCorrect]
  constructor
  · rw [orderingCode_zero]
    exact (ONote.cmp_compares a.1 b.1).eq_lt
  constructor
  · rw [orderingCode_one, (ONote.cmp_compares a.1 b.1).eq_eq]
    exact ONote.repr_inj.symm
  · rw [orderingCode_two]
    exact (ONote.cmp_compares a.1 b.1).eq_gt

end LogicLineages.OrdinalComparison
