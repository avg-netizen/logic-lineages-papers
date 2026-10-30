module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalizer
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductProof

@[expose] public section

/-! Structural soundness of the literal source normalizer. This Codex-authored
proof is separate from the read-only author's N2 supplier. The independent
normalization comparator was compiled before this proof was written.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProof

open PositiveExpression ExponentialNormalForm ExponentialNormalFormProduct
open ExponentialNormalizer ExponentialNormalFormProof

theorem affineVariable_value {d : Nat} (i : Fin d) (ρ : Fin d → Nat) :
    affineValue (affineVariable i) ρ = ρ i := by
  classical
  simp [affineValue, affineVariable]

theorem variableLaws : Comparators.ExponentialNormalizer.Variables := by
  intro d h i ρ
  cases h with
  | zero =>
      exact ⟨affineVariable_value i ρ, by simp [constantCoefficient,
        variableForm, affineVariable], True.intro⟩
  | succ h =>
      refine ⟨?_, ?_, ?_⟩
      · change Finsupp.sum (Finsupp.single (zeroForm h) (affineVariable i))
          (fun key coeff => affineValue coeff ρ * 2 ^ value h key ρ) = ρ i
        rw [Finsupp.sum_single_index]
        · rw [affineVariable_value, zero_value, Nat.pow_zero, Nat.mul_one]
        · rw [affineValue_zero, Nat.zero_mul]
      · simp [constantCoefficient, variableForm, affineVariable]
      · intro key hk
        have hz : key = zeroForm h :=
          Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
        subst key
        exact ⟨zero_wellFormed h, zero_coeff h⟩

theorem product_value {d : Nat} (h : Nat) (f g : Form d h) (ρ : Fin d → Nat) :
    value (h + 1) (exponentialProduct h f g) ρ =
      2 ^ value h f ρ * value h g ρ :=
  (ExponentialNormalFormProductProof.normalFormProduct.2.2 d h f g ρ).1

theorem product_wellFormed {d : Nat} (h : Nat) (f g : Form d h)
    (hf : WellFormed h f) (hg : WellFormed h g) :
    WellFormed (h + 1) (exponentialProduct h f g) :=
  (ExponentialNormalFormProductProof.normalFormProduct.2.2 d h f g
    (fun _ => 0)).2 hf hg

theorem boundedNormalization : Comparators.ExponentialNormalizer.BoundedNormalization := by
  intro d a
  induction a with
  | one =>
      intro h _
      exact ⟨const_wellFormed h 1, fun ρ => const_value h 1 (fun i => (ρ i : Nat))⟩
  | var i =>
      intro h _
      exact ⟨(variableLaws d h i (fun _ => 0)).2.2,
        fun ρ => (variableLaws d h i (fun j => (ρ j : Nat))).1⟩
  | add a b ha hb =>
      intro h hd
      have hA := ha h (Nat.le_trans (Nat.le_max_left _ _) hd)
      have hB := hb h (Nat.le_trans (Nat.le_max_right _ _) hd)
      refine ⟨add_wellFormed h _ _ hA.1 hB.1, ?_⟩
      intro ρ
      change value h (addForm h (normalizeAt a h) (normalizeAt b h))
        (fun i => (ρ i : Nat)) = a.eval ρ + b.eval ρ
      rw [add_value, hA.2 ρ, hB.2 ρ]
  | emul a b ha hb =>
      intro h hd
      cases h with
      | zero => simp [Expr.depth] at hd
      | succ h =>
          have hab : max a.depth b.depth ≤ h := by simpa [Expr.depth] using hd
          have hA := ha h (Nat.le_trans (Nat.le_max_left _ _) hab)
          have hB := hb h (Nat.le_trans (Nat.le_max_right _ _) hab)
          refine ⟨product_wellFormed h _ _ hA.1 hB.1, ?_⟩
          intro ρ
          change value (h + 1) (exponentialProduct h (normalizeAt a h)
            (normalizeAt b h)) (fun i => (ρ i : Nat)) = 2 ^ a.eval ρ * b.eval ρ
          rw [product_value, hA.2 ρ, hB.2 ρ]

theorem sourceNormalization : Comparators.ExponentialNormalizer.Target :=
  ⟨variableLaws, boundedNormalization,
    fun d a => boundedNormalization d a a.depth (Nat.le_refl _)⟩

end LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProof
