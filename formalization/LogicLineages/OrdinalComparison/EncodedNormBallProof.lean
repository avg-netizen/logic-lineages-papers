module
public import LogicLineages.OrdinalComparison.EncodedNormBallTargets
public import LogicLineages.OrdinalComparison.RawNormalProof
public import LogicLineages.OrdinalComparison.RawNormCode
public import LogicLineages.OrdinalComparison.NormBalls
public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem pair_mono {a b c d : Nat} (h₁ : a ≤ c) (h₂ : b ≤ d) :
    Nat.pair a b ≤ Nat.pair c d := by
  have hleft : Nat.pair a b ≤ Nat.pair c b := by
    rcases lt_or_eq_of_le h₁ with h | rfl
    · exact (Nat.pair_lt_pair_left b h).le
    · exact le_rfl
  have hright : Nat.pair c b ≤ Nat.pair c d := by
    rcases lt_or_eq_of_le h₂ with h | rfl
    · exact (Nat.pair_lt_pair_right c h).le
    · exact le_rfl
  exact hleft.trans hright

theorem rawNormCodeBoundCorrect : Targets.RawNormCodeBoundCorrect := by
  intro b
  induction b with
  | zero =>
      intro a ha
      have heq : a = 0 := (treeWeight_eq_zero_iff a).mp (Nat.eq_zero_of_le_zero ha)
      subst a
      exact le_rfl
  | succ b ih =>
      intro a ha
      cases a with
      | zero => exact Nat.zero_le _
      | oadd e c t =>
          have hc : 1 ≤ (c : Nat) := Nat.succ_le_of_lt c.pos
          have hfactor : 1 ≤ 1 + Vendor.R1.treeWeight e := by omega
          have hprod : 1 + Vendor.R1.treeWeight e ≤ (c : Nat) * (1 + Vendor.R1.treeWeight e) := by
            simpa only [Nat.one_mul] using Nat.mul_le_mul_right (1 + Vendor.R1.treeWeight e) hc
          have hcoef : (c : Nat) ≤ (c : Nat) * (1 + Vendor.R1.treeWeight e) := by
            simpa only [Nat.mul_one] using Nat.mul_le_mul_left (c : Nat) hfactor
          have he : Vendor.R1.treeWeight e ≤ b := by
            simp only [Vendor.R1.treeWeight] at ha
            omega
          have ht : Vendor.R1.treeWeight t ≤ b := by
            simp only [Vendor.R1.treeWeight] at ha
            omega
          have hcb : (c : Nat) - 1 ≤ b := by
            simp only [Vendor.R1.treeWeight] at ha
            omega
          exact Nat.add_le_add_right (pair_mono (ih e he) (pair_mono hcb (ih t ht))) 1

theorem encodedNormalNormBallCorrect : Targets.EncodedNormalNormBallCorrect := by
  intro b a
  simp only [encodedNormalNormBall, List.mem_filter, List.mem_range, decide_eq_true_eq,
    rawNormalCorrect a, rawNormCodeCorrect a]
  constructor
  · rintro ⟨_, hnormal, hnorm⟩
    exact ⟨hnormal, hnorm⟩
  · rintro ⟨hnormal, hnorm⟩
    exact ⟨Nat.lt_succ_of_le (rawNormCodeBoundCorrect b a hnorm), hnormal, hnorm⟩

theorem encodedNormalNormBallDecodeCorrect : Targets.EncodedNormalNormBallDecodeCorrect := by
  intro b n
  simpa only [rawNoteEncodeDecode n] using encodedNormalNormBallCorrect b (rawNoteDecode n)

private theorem rawNormCodeBound_primrec : Primrec rawNormCodeBound := by
  let step : Nat → Nat → Nat := fun b r => Nat.pair r (Nat.pair b r) + 1
  have hstep : Primrec₂ step := Primrec.succ.comp
    (Primrec₂.natPair.comp Primrec.snd (Primrec₂.natPair.comp Primrec.fst Primrec.snd))
  exact (Primrec.nat_rec₁ 0 hstep).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change step n (Nat.rec 0 step n) = _
        rw [ih]
        rfl)

theorem encodedNormalNormBallPrimitiveRecursive : Targets.EncodedNormalNormBallPrimitiveRecursive := by
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hf : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hp : PrimrecRel (fun n b : Nat => rawNormalCode n = 1 ∧ rawNormCode n ≤ b) :=
    (Primrec.eq.comp (hf.comp Primrec.fst) (Primrec.const 1)).and
      (Primrec.nat_le.comp (hn.comp Primrec.fst) Primrec.snd)
  exact hp.listFilter.comp (Primrec.list_range.comp (Primrec.succ.comp rawNormCodeBound_primrec)) Primrec.id

end LogicLineages.OrdinalComparison
