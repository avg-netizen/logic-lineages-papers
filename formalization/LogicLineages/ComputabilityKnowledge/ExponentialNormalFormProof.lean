module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalForm
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section

/-!
# The N1/N2 algebra of hereditary finite-map normal forms (paper 02)

Proves the frozen `Comparators.ExponentialNormalForm.Target`: exact values,
syntactic constant coefficients and well-formedness of zero and constants;
additivity of value and coefficient under the actual finite-map addition with
preservation of well-formedness; and the exact form decomposition
`F = c(F) + F°` with `F°` constant-free and well-formed. Affine facts use
`Fin.cases`; height-successor facts use `Finsupp` sum, single, update and
support lemmas.
-/

namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProof

open LogicLineages.ComputabilityKnowledge.ExponentialNormalForm
open LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalForm

/-! ## Affine coefficient vectors -/

theorem affineConstant_zero {d : Nat} (n : Nat) : affineConstant (d := d) n 0 = n := by
  simp [affineConstant]

theorem affineConstant_succ {d : Nat} (n : Nat) (i : Fin d) :
    affineConstant (d := d) n i.succ = 0 := by
  simp [affineConstant]

theorem affineRemove_zero {d : Nat} (a : Affine d) : affineRemoveConstant a 0 = 0 := by
  simp [affineRemoveConstant]

theorem affineRemove_succ {d : Nat} (a : Affine d) (i : Fin d) :
    affineRemoveConstant a i.succ = a i.succ := by
  simp [affineRemoveConstant]

theorem affineValue_zero {d : Nat} (ρ : Fin d → Nat) : affineValue (0 : Affine d) ρ = 0 := by
  unfold affineValue
  simp

theorem affineValue_add {d : Nat} (a b : Affine d) (ρ : Fin d → Nat) :
    affineValue (a + b) ρ = affineValue a ρ + affineValue b ρ := by
  unfold affineValue
  simp only [Pi.add_apply, Nat.add_mul, Finset.sum_add_distrib]
  omega

theorem affineValue_constant {d : Nat} (n : Nat) (ρ : Fin d → Nat) :
    affineValue (affineConstant (d := d) n) ρ = n := by
  simp only [affineValue, affineConstant_zero, affineConstant_succ, Nat.zero_mul,
    Finset.sum_const_zero, Nat.add_zero]

theorem affine_decompose {d : Nat} (a : Affine d) :
    affineConstant (a 0) + affineRemoveConstant a = a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show affineConstant (a 0) 0 + affineRemoveConstant a 0 = a 0
    rw [affineConstant_zero, affineRemove_zero, Nat.add_zero]
  · show affineConstant (a 0) j.succ + affineRemoveConstant a j.succ = a j.succ
    rw [affineConstant_succ, affineRemove_succ, Nat.zero_add]

/-! ## Zero and constants -/

theorem zero_value {d : Nat} : (h : Nat) → (ρ : Fin d → Nat) →
    value h (zeroForm (d := d) h) ρ = 0
  | 0, ρ => affineValue_zero ρ
  | h + 1, ρ => by
      show Finsupp.sum (0 : Form d h →₀ Affine d)
        (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ) = 0
      exact Finsupp.sum_zero_index

theorem zero_coeff {d : Nat} : (h : Nat) → constantCoefficient h (zeroForm (d := d) h) = 0
  | 0 => rfl
  | _ + 1 => rfl

theorem zero_wellFormed {d : Nat} : (h : Nat) → WellFormed h (zeroForm (d := d) h)
  | 0 => True.intro
  | h + 1 => by
      intro key hk
      exact absurd hk (Finset.notMem_empty key)

theorem const_value {d : Nat} : (h : Nat) → (n : Nat) → (ρ : Fin d → Nat) →
    value h (constantForm (d := d) h n) ρ = n
  | 0, n, ρ => affineValue_constant n ρ
  | h + 1, n, ρ => by
      show Finsupp.sum (Finsupp.single (zeroForm (d := d) h) (affineConstant (d := d) n))
        (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ) = n
      rw [Finsupp.sum_single_index]
      · rw [affineValue_constant, zero_value, Nat.pow_zero, Nat.mul_one]
      · rw [affineValue_zero, Nat.zero_mul]

theorem const_coeff {d : Nat} : (h : Nat) → (n : Nat) →
    constantCoefficient h (constantForm (d := d) h n) = n
  | 0, n => by simp [constantCoefficient, constantForm, affineConstant]
  | h + 1, n => by
      show (Finsupp.single (zeroForm (d := d) h) (affineConstant (d := d) n))
        (zeroForm h) 0 = n
      rw [Finsupp.single_eq_same, affineConstant_zero]

theorem const_wellFormed {d : Nat} : (h : Nat) → (n : Nat) →
    WellFormed h (constantForm (d := d) h n)
  | 0, _ => True.intro
  | h + 1, n => by
      intro key hk
      have hz : key = zeroForm h :=
        Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
      subst hz
      exact ⟨zero_wellFormed h, zero_coeff h⟩

theorem zeroAndConstants : ZeroAndConstants := by
  intro d h ρ
  exact ⟨zero_value h ρ, zero_coeff h, zero_wellFormed h,
    fun n => ⟨const_value h n ρ, const_coeff h n, const_wellFormed h n⟩⟩

/-! ## Addition -/

theorem add_value {d : Nat} : (h : Nat) → (f g : Form d h) → (ρ : Fin d → Nat) →
    value h (addForm h f g) ρ = value h f ρ + value h g ρ
  | 0, f, g, ρ => affineValue_add f g ρ
  | h + 1, f, g, ρ => by
      show Finsupp.sum (f + g) (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ) =
        Finsupp.sum f (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ) +
        Finsupp.sum g (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ)
      exact Finsupp.sum_add_index'
        (fun key => by rw [affineValue_zero, Nat.zero_mul])
        (fun key a b => by rw [affineValue_add, Nat.add_mul])

theorem add_coeff {d : Nat} : (h : Nat) → (f g : Form d h) →
    constantCoefficient h (addForm h f g) = constantCoefficient h f + constantCoefficient h g
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem add_wellFormed {d : Nat} : (h : Nat) → (f g : Form d h) →
    WellFormed h f → WellFormed h g → WellFormed h (addForm h f g)
  | 0, _, _, _, _ => True.intro
  | h + 1, f, g, hf, hg => by
      classical
      intro key hk
      rcases Finset.mem_union.mp (Finsupp.support_add hk) with h1 | h2
      · exact hf key h1
      · exact hg key h2

theorem addition : Addition := by
  intro d h f g ρ
  exact ⟨add_value h f g ρ, add_coeff h f g, add_wellFormed h f g⟩

/-! ## Removing the syntactic constant -/

theorem remove_coeff {d : Nat} : (h : Nat) → (f : Form d h) →
    constantCoefficient h (removeConstant h f) = 0
  | 0, f => affineRemove_zero f
  | h + 1, f => by
      classical
      show (Finsupp.update f (zeroForm h) (affineRemoveConstant (f (zeroForm h))))
        (zeroForm h) 0 = 0
      rw [Finsupp.update_apply, if_pos rfl, affineRemove_zero]

theorem remove_decompose {d : Nat} : (h : Nat) → (f : Form d h) →
    addForm h (constantForm h (constantCoefficient h f)) (removeConstant h f) = f
  | 0, f => affine_decompose f
  | h + 1, f => by
      classical
      show Finsupp.single (zeroForm h) (affineConstant (f (zeroForm h) 0)) +
          Finsupp.update f (zeroForm h) (affineRemoveConstant (f (zeroForm h))) = f
      apply Finsupp.ext
      intro k
      rw [Finsupp.add_apply, Finsupp.update_apply]
      by_cases hk : k = zeroForm h
      · subst hk
        rw [if_pos rfl, Finsupp.single_eq_same]
        exact affine_decompose (f (zeroForm h))
      · rw [if_neg hk, Finsupp.single_eq_of_ne hk, zero_add]

theorem remove_wellFormed {d : Nat} : (h : Nat) → (f : Form d h) →
    WellFormed h f → WellFormed h (removeConstant h f)
  | 0, _, _ => True.intro
  | h + 1, f, hf => by
      classical
      intro key hk
      change key ∈ (f.update (zeroForm h) (affineRemoveConstant (f (zeroForm h)))).support at hk
      have hk' := (Finsupp.support_update_subset f (zeroForm h)
        (b := affineRemoveConstant (f (zeroForm h)))) hk
      rcases Finset.mem_insert.mp hk' with h1 | h2
      · subst key
        exact ⟨zero_wellFormed h, zero_coeff h⟩
      · exact hf key h2

theorem removeSyntacticConstant : RemoveSyntacticConstant := by
  intro d h f
  exact ⟨remove_coeff h f, remove_decompose h f, remove_wellFormed h f⟩

theorem normalFormAlgebra :
    LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalForm.Target := by
  exact ⟨zeroAndConstants, addition, removeSyntacticConstant⟩

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProof
