module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BinomialProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingProof
open Dioph MaskingTargets

private theorem bit_eq (a b : Bool) (m n : Nat) :
    Nat.bit a m = Nat.bit b n ↔ a = b ∧ m = n := by
  cases a <;> cases b <;> simp [Nat.bit_val] <;> omega

private theorem binary_decomposition (n : Nat) : ∃ (b : Bool) (k : Nat), n = Nat.bit b k :=
  ⟨n.bodd, n.div2, (Nat.bit_bodd_div2 n).symm⟩

theorem bitMaskParity : BitMaskParity := by
  intro a b
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  induction b using Nat.binaryRec generalizing a with
  | zero => cases a <;> simp
  | bit bb b ih =>
      obtain ⟨ba, a, rfl⟩ := binary_decomposition a
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := Nat.bit bb b) (k := Nat.bit ba a) (p := 2)
      change Nat.choose (Nat.bit bb b) (Nat.bit ba a) % 2 =
        (Nat.choose (Nat.bit bb b % 2) (Nat.bit ba a % 2) *
          Nat.choose (Nat.bit bb b / 2) (Nat.bit ba a / 2)) % 2 at h
      rw [Nat.bit_mod_two, Nat.bit_mod_two, Nat.bit_div_two, Nat.bit_div_two] at h
      rw [h, Nat.land_bit, bit_eq]
      cases ba <;> cases bb <;> simp [Nat.choose, ih]

theorem bitMaskDiophantine : BitMaskDiophantine := by
  intro alpha f g hf hg
  have h := Dioph.eq_dioph
    (Dioph.mod_dioph (BinomialProof.binomialDiophantine _ _ _ hg hf)
      (Dioph.const_dioph 2)) (Dioph.const_dioph 1)
  exact h.ext (fun v => bitMaskParity (f v) (g v))

private theorem mask_le (a b : Nat) (h : a &&& b = a) : a ≤ b := by
  induction a using Nat.binaryRec generalizing b with
  | zero => exact Nat.zero_le _
  | bit ba a ih =>
      obtain ⟨bb, b, rfl⟩ := binary_decomposition b
      have hb := (bit_eq _ _ _ _).mp (by simpa only [Nat.land_bit] using h)
      have hl : a ≤ b := ih b hb.2
      have hlow := hb.1
      cases ba <;> cases bb <;> simp only [Nat.bit_false_apply, Nat.bit_true_apply]
      all_goals simp at hlow
      all_goals omega

private theorem intersection_mask (a b : Nat) : (a &&& b) &&& a = a &&& b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem bitAndCharacterization : BitAndCharacterization := by
  intro a b c
  induction a using Nat.binaryRec generalizing b c with
  | zero => simp [eq_comm]
  | bit ba a ih =>
      obtain ⟨bb, b, rfl⟩ := binary_decomposition b
      obtain ⟨bc, c, rfl⟩ := binary_decomposition c
      by_cases hca : Nat.bit bc c &&& Nat.bit ba a = Nat.bit bc c
      · have hc := (bit_eq _ _ _ _).mp (by simpa only [Nat.land_bit] using hca)
        have hl : c ≤ a := mask_le c a hc.2
        have hi : a &&& b = c ↔ a &&& (a+b-c) = a := by
          simpa [hc.2] using ih b c
        simp only [hca, true_and]
        cases ba with
        | false =>
            cases bc with
            | true => simp at hc
            | false =>
                cases bb with
                | false =>
                    have hd : Nat.bit false a + Nat.bit false b - Nat.bit false c =
                        Nat.bit false (a+b-c) := by simp only [Nat.bit_false_apply]; omega
                    rw [hd, Nat.land_bit, Nat.land_bit, bit_eq, bit_eq]
                    simpa using hi
                | true =>
                    have hd : Nat.bit false a + Nat.bit true b - Nat.bit false c =
                        Nat.bit true (a+b-c) := by
                      simp only [Nat.bit_false_apply, Nat.bit_true_apply]; omega
                    rw [hd, Nat.land_bit, Nat.land_bit, bit_eq, bit_eq]
                    simpa using hi
        | true =>
            cases bc with
            | false =>
                cases bb with
                | false =>
                    have hd : Nat.bit true a + Nat.bit false b - Nat.bit false c =
                        Nat.bit true (a+b-c) := by
                      simp only [Nat.bit_false_apply, Nat.bit_true_apply]; omega
                    rw [hd, Nat.land_bit, Nat.land_bit, bit_eq, bit_eq]
                    simpa using hi
                | true =>
                    have hd : Nat.bit true a + Nat.bit true b - Nat.bit false c =
                        Nat.bit false (a+b-c+1) := by
                      simp only [Nat.bit_false_apply, Nat.bit_true_apply]; omega
                    rw [hd, Nat.land_bit, Nat.land_bit, bit_eq, bit_eq]
                    simp
            | true =>
                cases bb with
                | false =>
                    have hd : Nat.bit true a + Nat.bit false b - Nat.bit true c =
                        Nat.bit false (a+b-c) := by
                      simp only [Nat.bit_false_apply, Nat.bit_true_apply]; omega
                    rw [hd, Nat.land_bit, Nat.land_bit, bit_eq, bit_eq]
                    simp
                | true =>
                    have hd : Nat.bit true a + Nat.bit true b - Nat.bit true c =
                        Nat.bit true (a+b-c) := by
                      simp only [Nat.bit_true_apply]; omega
                    rw [hd, Nat.land_bit, Nat.land_bit, bit_eq, bit_eq]
                    simpa using hi
      · simp only [hca, false_and, iff_false]
        intro h
        apply hca
        rw [← h]
        exact intersection_mask _ _

theorem bitAndDiophantine : BitAndDiophantine := by
  intro alpha f g hf hg
  have hF : DiophFn (fun v : Option alpha → Nat => f (v ∘ some)) :=
    Dioph.reindex_diophFn some hf
  have hG : DiophFn (fun v : Option alpha → Nat => g (v ∘ some)) :=
    Dioph.reindex_diophFn some hg
  have hO : DiophFn (fun v : Option alpha → Nat => v none) := Dioph.proj_dioph none
  have h1 := bitMaskDiophantine _ _ _ hO hF
  have h2 := bitMaskDiophantine _ _ _ hF
    (Dioph.sub_dioph (Dioph.add_dioph hF hG) hO)
  exact (h1.inter h2).ext
    (fun v => (bitAndCharacterization (f (v ∘ some)) (g (v ∘ some)) (v none)).symm)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingProof
