module
public import LogicLineages.OrdinalComparison.RawSplitTargets
public import LogicLineages.OrdinalComparison.RawNotationCode
public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace LogicLineages.OrdinalComparison

private def sourceSplitCode (n : Nat) : Nat :=
  Nat.pair (rawNoteEncode (ONote.split (rawNoteDecode n)).1) (ONote.split (rawNoteDecode n)).2

private theorem decode_eq_zero_iff (n : Nat) : rawNoteDecode n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have he := congrArg rawNoteEncode h
    rw [rawNoteEncodeDecode n] at he
    exact he
  · intro h
    subst n
    exact (rawNoteDecodeEquation).1

private theorem rawSplitStep_correct (n : Nat) (table : List Nat)
    (h : ∀ i : Nat, i < n → table.getD i 0 = sourceSplitCode i) :
    rawSplitStep n table = sourceSplitCode n := by
  cases n with
  | zero => simp [rawSplitStep, sourceSplitCode, rawNoteDecode, ONote.split, rawNoteEncode]; rfl
  | succ n =>
      have ht := h n.unpair.2.unpair.2
        (Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n)))
      simp only [sourceSplitCode] at ht ⊢
      rw [(rawNoteDecodeEquation).2 n]
      by_cases he : n.unpair.1 = 0
      · have hd : rawNoteDecode n.unpair.1 = 0 := (decode_eq_zero_iff _).mpr he
        simp [rawSplitStep, he, (rawNoteDecodeEquation).1, ONote.split, rawNoteEncode]
      · have hd : rawNoteDecode n.unpair.1 ≠ 0 := (decode_eq_zero_iff _).not.mpr he
        simp only [rawSplitStep, Nat.succ_ne_zero, ↓reduceIte, Nat.pred_succ, he, hd,
          ONote.split]
        rw [ht]
        simp [Nat.unpair_pair, rawNoteEncode, rawNoteEncodeDecode n.unpair.1]

private theorem rawSplitTable_length (n : Nat) : (rawSplitTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rawSplitTable, List.length_append, List.length_singleton, ih]

private theorem rawSplitTable_correct (n : Nat) :
    ∀ i : Nat, i ≤ n → (rawSplitTable n).getD i 0 = sourceSplitCode i := by
  induction n with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [rawSplitTable, sourceSplitCode, rawNoteDecode, ONote.split, rawNoteEncode]
      rfl
  | succ n ih =>
      intro i hi
      by_cases hin : i ≤ n
      · rw [rawSplitTable, List.getD_append _ _ _ _ (by rw [rawSplitTable_length]; omega)]
        exact ih i hin
      · have hieq : i = n + 1 := by omega
        subst i
        rw [rawSplitTable, List.getD_append_right _ _ _ _ (by rw [rawSplitTable_length])]
        simp only [rawSplitTable_length, Nat.sub_self, List.getD_cons_zero]
        exact rawSplitStep_correct _ _ (fun j hj => ih j (by omega))

theorem rawSplitCorrect : Targets.RawSplitCorrect := by
  intro a
  have h := rawSplitTable_correct (rawNoteEncode a) (rawNoteEncode a) le_rfl
  simpa only [rawSplitCode, sourceSplitCode, rawNoteDecodeEncode a] using h

theorem rawSplitNormal : Targets.RawSplitNormal := by
  intro a
  rcases hs : ONote.split a.1 with ⟨l, n⟩
  have hn := (ONote.nf_repr_split hs).1
  rw [rawSplitCorrect a.1, hs, Nat.unpair_pair, rawNoteDecodeEncode l]
  exact hn

theorem rawSplitActualCorrect : Targets.RawSplitActualCorrect := by
  intro a
  rcases hs : ONote.split' a.1 with ⟨q, n⟩
  have hn := ONote.nf_repr_split' hs
  letI : ONote.NF q := hn.1
  have hsplit := ONote.split_eq_scale_split' hs
  have hscale : (ONote.scale 1 q).repr = Ordinal.omega0 * q.repr := by
    simpa using ONote.repr_scale (1 : ONote) q
  have hdiv : a.1.repr / Ordinal.omega0 = q.repr := by
    rw [hn.2, Ordinal.mul_add_div _ Ordinal.omega0_ne_zero _,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]
  have hmod : a.1.repr % Ordinal.omega0 = (n : Ordinal) := by
    rw [hn.2, Ordinal.mul_add_mod_self,
      Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 n)]
  rw [rawSplitCorrect a.1, hsplit]
  simp only [Nat.unpair_pair, rawNoteDecodeEncode (ONote.scale 1 q)]
  constructor
  · rw [hscale, actualLimitPart, hdiv]
  · rw [actualTailPart, hmod, Ordinal.card_nat, Cardinal.toNat_natCast]

private theorem rawSplitStep_primrec : Primrec₂ rawSplitStep := by
  have hfields := Primrec.unpair.comp
    (Primrec.nat_sub.comp (Primrec.fst : Primrec (fun p : Nat × List Nat => p.1)) (Primrec.const 1))
  have he := Primrec.fst.comp hfields
  have hc := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hfields))
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hfields))
  have htail := Primrec.unpair.comp ((Primrec.list_getD 0).comp Primrec.snd ht)
  have hnode := Primrec.succ.comp
    (Primrec₂.natPair.comp he (Primrec₂.natPair.comp hc (Primrec.fst.comp htail)))
  have hrec := Primrec₂.natPair.comp hnode (Primrec.snd.comp htail)
  have hfinite := Primrec₂.natPair.comp (Primrec.const 0) (Primrec.succ.comp hc)
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp he (Primrec.const 0)) hfinite hrec)

theorem rawSplitPrimitiveRecursive : Targets.RawSplitPrimitiveRecursive := by
  let step : Nat → List Nat → List Nat := fun n table => table ++ [rawSplitStep (n + 1) table]
  have hstep : Primrec₂ step := Primrec.list_concat.comp Primrec.snd
    (rawSplitStep_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  have htable : Primrec rawSplitTable := (Primrec.nat_rec₁ [0] hstep).of_eq (by
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
