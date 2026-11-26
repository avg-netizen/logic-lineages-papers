module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidueLetterProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Proof
open PolynomialGraphCompletion

theorem literalWordResidue : Targets.LiteralWordResidue := by
  intro D m hm w
  induction w with
  | nil =>
      intro hw t ht
      exact ⟨trivial, by simpa [affine, wordValue] using (Int.ModEq.refl (t : Int))⟩
  | cons a w ih =>
      intro hw t ht
      have ha : LetterAllowed D a := hw a List.mem_cons_self
      have hwa : WordAllowed D w := fun b hb => hw b (List.mem_cons_of_mem a hb)
      change letterTail m a + WordGuardCompletion.letterOffset a + tail m w ≤ t at ht
      have hs := literalLetterResidue D m hm a ha t (by omega)
      have hg : WordGuardCompletion.letterTail a ≤ t := by
        have hl : letterTail m a ≤ t := by omega
        unfold letterTail at hl
        omega
      have hc := WordGuardCompletion.Proof.letterTailCorrect D a t ha hg
      have hn : tail m w ≤ letterValue a t := by omega
      have hi := ih hwa (letterValue a t) hn
      refine ⟨⟨hs.1, hi.1⟩, ?_⟩
      have hmul := (hs.2.mul_left (affine m w).1).add_right (affine m w).2
      have he := hi.2.trans hmul
      simpa only [wordValue, affine, mul_add, mul_assoc, add_assoc] using he

theorem exactSlope : Targets.ExactSlope := by
  intro m w
  induction w with
  | nil => simp [affine]
  | cons a w ih =>
      change (affine m w).1 * (letterAffine m a).1 =
        if ((a.1 == 0) && w.all (fun b : Letter => b.1 == 0)) then 1 else 0
      by_cases h : a.1 = 0
      · have hb : (a.1 == 0) = true := by simp [h]
        rw [hb]
        simpa only [Bool.true_and, letterAffine, if_pos h, mul_one] using ih
      · have hb : (a.1 == 0) = false := by simp [h]
        rw [hb]
        by_cases h4 : a.1 = 4 <;> simp [letterAffine, h, h4]

theorem literalShiftResidue : Targets.LiteralShiftResidue := by
  intro m w
  induction w with
  | nil => intro _; rfl
  | cons a w ih =>
      intro hw
      have ha : a.1 = 0 := hw a List.mem_cons_self
      have hs : ∀ b ∈ w, b.1 = 0 := fun b hb => hw b (List.mem_cons_of_mem a hb)
      simp [affine, letterAffine, ha, ih hs]

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Proof
