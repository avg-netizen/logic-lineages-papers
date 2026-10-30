module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormProduct
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProof
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Height transport and the literal N2 exponential constructor (paper 02)

Proves the frozen `Comparators.ExponentialNormalFormProduct.Target`. Raising is
`Finsupp.mapDomain` of the lower raising, hence injective, value- and
coefficient-preserving and normality-preserving by height induction. The
constructor `E(f,g)` evaluates to `2^f * g` by the accepted decomposition
`f = c(f) + f°`, finite distributivity and `2^(u+v) = 2^u 2^v`; its keys
`f° + raise e` are constant-free well-formed sums of accepted forms.
-/

namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductProof

open LogicLineages.ComputabilityKnowledge.ExponentialNormalForm
open LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProduct
open LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProof
open LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormProduct

/-! ## Affine scaling and finite-sum helpers -/

theorem affine_scale {d : Nat} (k : Nat) (a : Affine d) (ρ : Fin d → Nat) :
    affineValue (scaleAffine k a) ρ = k * affineValue a ρ := by
  simp only [affineValue, scaleAffine, Nat.mul_add, Finset.mul_sum, Nat.mul_assoc]

theorem affineScaling : AffineScaling := by
  intro d k a ρ
  exact affine_scale k a ρ

theorem mul_fsum {α M : Type*} [Zero M] (b : Nat) (s : α →₀ M) (F : α → M → Nat) :
    b * s.sum F = s.sum (fun a c => b * F a c) := by
  unfold Finsupp.sum
  rw [Finset.mul_sum]

theorem value_split {d : Nat} (h : Nat) (f : Form d h) (ρ : Fin d → Nat) :
    value h f ρ = constantCoefficient h f + value h (removeConstant h f) ρ := by
  have e : value h (addForm h (constantForm h (constantCoefficient h f))
      (removeConstant h f)) ρ = value h f ρ := by
    rw [remove_decompose]
  rw [add_value, const_value] at e
  exact e.symm

/-! ## Height transport -/

theorem raise_succ {d : Nat} (h : Nat) (f : Form d (h + 1)) :
    raiseForm (h + 1) f = Finsupp.mapDomain (raiseForm h) f := rfl

theorem raise_zero {d : Nat} : (h : Nat) → raiseForm h (zeroForm (d := d) h) = zeroForm (h + 1)
  | 0 => by
      show Finsupp.single (zeroForm (d := d) 0) (0 : Affine d) = 0
      exact Finsupp.single_zero _
  | h + 1 => by
      show Finsupp.sum (0 : Form d h →₀ Affine d)
        (fun key coeff => Finsupp.single (raiseForm h key) coeff) = 0
      exact Finsupp.sum_zero_index

theorem raise_injective {d : Nat} : (h : Nat) → Function.Injective (raiseForm (d := d) h)
  | 0 => by
      intro f g hfg
      exact Finsupp.single_injective (zeroForm (d := d) 0) hfg
  | h + 1 => by
      intro f g hfg
      rw [raise_succ, raise_succ] at hfg
      exact Finsupp.mapDomain_injective (raise_injective h) hfg

theorem raise_value {d : Nat} : (h : Nat) → (f : Form d h) → (ρ : Fin d → Nat) →
    value (h + 1) (raiseForm h f) ρ = value h f ρ
  | 0, f, ρ => by
      show Finsupp.sum (Finsupp.single (zeroForm (d := d) 0) (f : Affine d))
        (fun key coeff => affineValue coeff ρ * 2 ^ value 0 key ρ) = affineValue f ρ
      rw [Finsupp.sum_single_index]
      · rw [zero_value, Nat.pow_zero, Nat.mul_one]
      · rw [affineValue_zero, Nat.zero_mul]
  | h + 1, f, ρ => by
      show Finsupp.sum (Finsupp.sum f (fun k c => Finsupp.single (raiseForm h k) c))
          (fun key coeff => affineValue coeff ρ * 2 ^ value (h + 1) key ρ) =
        Finsupp.sum f (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ)
      rw [Finsupp.sum_sum_index]
      · apply Finsupp.sum_congr
        intro key _
        rw [Finsupp.sum_single_index]
        · rw [raise_value h key ρ]
        · rw [affineValue_zero, Nat.zero_mul]
      · intro b
        rw [affineValue_zero, Nat.zero_mul]
      · intro b m₁ m₂
        rw [affineValue_add, Nat.add_mul]

theorem raise_coeff {d : Nat} : (h : Nat) → (f : Form d h) →
    constantCoefficient (h + 1) (raiseForm h f) = constantCoefficient h f
  | 0, f => by
      show (Finsupp.single (zeroForm (d := d) 0) (f : Affine d)) (zeroForm 0) 0 = f 0
      rw [Finsupp.single_eq_same]
  | h + 1, f => by
      show (Finsupp.mapDomain (raiseForm h) f) (zeroForm (h + 1)) 0 = f (zeroForm h) 0
      rw [← raise_zero h, Finsupp.mapDomain_apply (raise_injective h)]

theorem raise_wellFormed {d : Nat} : (h : Nat) → (f : Form d h) →
    WellFormed h f → WellFormed (h + 1) (raiseForm h f)
  | 0, f, _ => by
      intro key hk
      change key ∈ (Finsupp.single (zeroForm (d := d) 0) (f : Affine d)).support at hk
      have hz := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
      subst hz
      exact ⟨zero_wellFormed 0, zero_coeff 0⟩
  | h + 1, f, hf => by
      classical
      intro key hk
      change key ∈ (Finsupp.sum f (fun k c => Finsupp.single (raiseForm h k) c)).support at hk
      obtain ⟨k, hk1, hk2⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hk)
      have hz := Finset.mem_singleton.mp (Finsupp.support_single_subset hk2)
      subst hz
      obtain ⟨hwk, hck⟩ := hf k hk1
      exact ⟨raise_wellFormed h k hwk, (raise_coeff h k).trans hck⟩

theorem heightTransport : HeightTransport := by
  intro d h
  exact ⟨raise_zero h, raise_injective h, fun f ρ =>
    ⟨raise_value h f ρ, raise_coeff h f, raise_wellFormed h f⟩⟩

/-! ## The literal N2 exponential product -/

theorem exp_value {d : Nat} : (h : Nat) → (f g : Form d h) → (ρ : Fin d → Nat) →
    value (h + 1) (exponentialProduct h f g) ρ = 2 ^ value h f ρ * value h g ρ
  | 0, f, g, ρ => by
      show Finsupp.sum (Finsupp.single (removeConstant 0 f)
          (scaleAffine (2 ^ constantCoefficient 0 f) (g : Affine d)))
          (fun key coeff => affineValue coeff ρ * 2 ^ value 0 key ρ) =
        2 ^ value 0 f ρ * affineValue g ρ
      rw [Finsupp.sum_single_index]
      · rw [affine_scale, value_split 0 f ρ, Nat.pow_add]
        exact Nat.mul_right_comm _ _ _
      · rw [affineValue_zero, Nat.zero_mul]
  | h + 1, f, g, ρ => by
      show Finsupp.sum (Finsupp.sum g (fun key coeff =>
          Finsupp.single (addForm (h + 1) (removeConstant (h + 1) f) (raiseForm h key))
            (scaleAffine (2 ^ constantCoefficient (h + 1) f) coeff)))
          (fun key coeff => affineValue coeff ρ * 2 ^ value (h + 1) key ρ) =
        2 ^ value (h + 1) f ρ *
          Finsupp.sum g (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ)
      rw [Finsupp.sum_sum_index, mul_fsum]
      · apply Finsupp.sum_congr
        intro key _
        rw [Finsupp.sum_single_index]
        · rw [affine_scale, add_value, raise_value, value_split (h + 1) f ρ,
            Nat.pow_add, Nat.pow_add]
          ring
        · rw [affineValue_zero, Nat.zero_mul]
      · intro b
        rw [affineValue_zero, Nat.zero_mul]
      · intro b m₁ m₂
        rw [affineValue_add, Nat.add_mul]

theorem exp_wellFormed {d : Nat} : (h : Nat) → (f g : Form d h) →
    WellFormed h f → WellFormed h g → WellFormed (h + 1) (exponentialProduct h f g)
  | 0, f, g, _, _ => by
      intro key hk
      change key ∈ (Finsupp.single (removeConstant 0 f)
        (scaleAffine (2 ^ constantCoefficient 0 f) (g : Affine d))).support at hk
      have hz := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
      subst hz
      exact ⟨True.intro, remove_coeff 0 f⟩
  | h + 1, f, g, hf, hg => by
      classical
      intro key hk
      change key ∈ (Finsupp.sum g (fun k coeff =>
        Finsupp.single (addForm (h + 1) (removeConstant (h + 1) f) (raiseForm h k))
          (scaleAffine (2 ^ constantCoefficient (h + 1) f) coeff))).support at hk
      obtain ⟨k, hk1, hk2⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hk)
      have hz := Finset.mem_singleton.mp (Finsupp.support_single_subset hk2)
      subst hz
      obtain ⟨hwk, hck⟩ := hg k hk1
      refine ⟨add_wellFormed (h + 1) _ _ (remove_wellFormed (h + 1) f hf)
        (raise_wellFormed h k hwk), ?_⟩
      rw [add_coeff, remove_coeff, raise_coeff, hck, Nat.add_zero]

theorem sourceExponentialProduct : SourceExponentialProduct := by
  intro d h f g ρ
  exact ⟨exp_value h f g ρ, exp_wellFormed h f g⟩

theorem normalFormProduct :
    LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormProduct.Target := by
  exact ⟨affineScaling, heightTransport, sourceExponentialProduct⟩

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductProof
