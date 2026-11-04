module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BinomialTargets
public import Mathlib.Data.List.GetD

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BinomialProof
open Dioph BinomialTargets
open scoped BigOperators

private theorem ofDigits_range (u m : Nat) (f : Nat → Nat) :
    Nat.ofDigits u ((List.range m).map f) = ∑ i ∈ Finset.range m, f i * u^i := by
  induction m with
  | zero => simp [Nat.ofDigits]
  | succ m ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton,
        Nat.ofDigits_append, List.length_map, List.length_range,
        Nat.ofDigits_singleton, Finset.sum_range_succ]
      rw [ih]
      simp [Nat.mul_comm]

theorem binomialDigitReconstruction : BinomialDigitReconstruction := by
  intro n u
  rw [ofDigits_range]
  symm
  simpa [Nat.mul_comm] using (add_pow u 1 n)

private theorem head_drop (digits : List Nat) (k : Nat) :
    (digits.drop k).head! = digits.getD k 0 := by
  induction k generalizing digits with
  | zero => cases digits <;> rfl
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a rest => exact ih rest

theorem naturalDigitExtraction : NaturalDigitExtraction := by
  intro u digits k hu hd
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop k hu digits hd,
    Nat.ofDigits_mod_eq_head!]
  have hh : (digits.drop k).head! < u := by
    cases heq : digits.drop k with
    | nil => simpa [heq] using hu
    | cons a rest =>
        have ha : a ∈ digits.drop k := by simp [heq]
        simpa [heq] using hd a (List.mem_of_mem_drop ha)
  rw [Nat.mod_eq_of_lt hh, head_drop]

theorem binomialDigitExtraction : BinomialDigitExtraction := by
  intro n k u hu
  have hd : ∀ a ∈ (List.range (n+1)).map (Nat.choose n), a < u := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact lt_of_le_of_lt (Nat.choose_le_two_pow n i) hu
  have hp : 0 < u := lt_trans (Nat.two_pow_pos n) hu
  have he := naturalDigitExtraction u ((List.range (n+1)).map (Nat.choose n)) k hp hd
  rw [binomialDigitReconstruction n u] at he
  have hg : ((List.range (n+1)).map (Nat.choose n)).getD k 0 = Nat.choose n k := by
    by_cases hk : k < n+1
    · rw [List.getD_eq_getElem _ 0 (by simpa using hk)]
      simp [hk]
    · rw [List.getD_eq_default _ 0 (by simp; omega)]
      exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  exact (he.trans hg).symm

theorem binomialDiophantine : BinomialDiophantine := by
  intro alpha f g hf hg
  have hU : DiophFn (fun v => 2^(f v+1)) :=
    Dioph.pow_dioph (Dioph.const_dioph 2)
      (Dioph.add_dioph hf (Dioph.const_dioph 1))
  have hP : DiophFn (fun v => (2^(f v+1)+1)^(f v)) :=
    Dioph.pow_dioph (Dioph.add_dioph hU (Dioph.const_dioph 1)) hf
  have hD : DiophFn (fun v => (2^(f v+1))^(g v)) := Dioph.pow_dioph hU hg
  have h := Dioph.mod_dioph (Dioph.div_dioph hP hD) hU
  have he : (fun v : alpha → Nat =>
      ((2^(f v+1)+1)^(f v) / (2^(f v+1))^(g v)) % (2^(f v+1))) =
      (fun v => Nat.choose (f v) (g v)) := by
    funext v
    exact (binomialDigitExtraction (f v) (g v) (2^(f v+1))
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))).symm
  exact he ▸ h

theorem binomialPolynomialRepresentation : BinomialPolynomialRepresentation := by
  apply (DiophantinePolynomialBridgeProof.diophantineCodeRepresentation 3 _).mp
  exact Dioph.eq_dioph
    (binomialDiophantine _ _ _ (Dioph.proj_dioph (0 : Fin 3))
      (Dioph.proj_dioph (1 : Fin 3))) (Dioph.proj_dioph (2 : Fin 3))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BinomialProof
