module
public import LogicLineages.OrdinalComparison.ConstantMonomialCountProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem constant_cut_multiple (d m : Nat)
    (h : ∀ a : Ordinal.{0}, a < Ordinal.omega0 ^ (d : Ordinal) → ∀ b : Nat,
      actualOrdinalNorm a ≤ b → Nat.ModEq m
        (actualControlledCount (fun _ => b + restrictedPartitionPeriod d m) a)
        (actualControlledCount (fun _ => b) a))
    (a : Ordinal) (ha : a < Ordinal.omega0 ^ (d : Ordinal)) (b : Nat)
    (hb : actualOrdinalNorm a ≤ b) (k : Nat) :
    Nat.ModEq m (actualControlledCount (fun _ => b + restrictedPartitionPeriod d m * k) a)
      (actualControlledCount (fun _ => b) a) := by
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.ModEq.refl _
  | succ k ih =>
    have hs := h a ha (b + restrictedPartitionPeriod d m * k) (by omega)
    simpa only [Nat.mul_succ, Nat.add_assoc] using hs.trans ih

private theorem modEq_cut_sum (m k : Nat) (f g : Nat → Nat)
    (h : ∀ j : Nat, j < k → Nat.ModEq m (f j) (g j)) :
    Nat.ModEq m (∑ j ∈ Finset.range k, f j) (∑ j ∈ Finset.range k, g j) := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact Nat.ModEq.refl _
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (ih (fun j hj => h j (Nat.lt_succ_of_lt hj))).add (h k (Nat.lt_succ_self k))

theorem actualConstantBudgetCutPeriod : Targets.ActualConstantBudgetCutPeriod := by
  intro d m hd hm
  induction d, hd using Nat.le_induction with
  | base =>
    intro a ha b _
    have haf : a < Ordinal.omega0 := by simpa only [Nat.cast_one, Ordinal.opow_one] using ha
    have homega : Ordinal.omega0 < epsilonZero := by
      simpa only [Nat.cast_one, Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1
    have hae : a < epsilonZero := haf.trans homega
    have h1 := (actualControlledCountRecursion (fun _ => b + restrictedPartitionPeriod 1 m) a hae).1 haf
    have h2 := (actualControlledCountRecursion (fun _ => b) a hae).1 haf
    rw [h1, h2]
  | succ d hd ih =>
    intro a ha b hb
    obtain ⟨v, hv⟩ := polynomialRawNoteOrdinalComplete (d + 1) a ha
    let k := v (Fin.last d)
    let p := Ordinal.omega0 ^ (d : Ordinal) * (k : Ordinal)
    let r := (polynomialRawNote d (Fin.init v)).repr
    have hp := actualFiniteMonomialFacts d k
    have hrraw := polynomialRawNoteNormalBoundNorm d (Fin.init v)
    have hreps : r < epsilonZero := normalRepresentationSound ⟨_, hrraw.1⟩
    have hrbound : r < Ordinal.omega0 ^ (d : Ordinal) := hrraw.2.1
    have haeq : a = p + r := hv.symm.trans (polynomialRawNoteLeadingDecomposition d v)
    obtain ⟨K, hK⟩ := restrictedPartitionPeriodDivisibility d (d + 1) m hd (Nat.le_succ d)
    have hres : ∀ B : Nat, actualOrdinalNorm r ≤ B →
        Nat.ModEq m (actualControlledCount (fun _ => B + restrictedPartitionPeriod (d + 1) m) r)
          (actualControlledCount (fun _ => B) r) := by
      intro B hB
      rw [hK]
      exact constant_cut_multiple d m ih r hrbound B hB K
    by_cases hk : k = 0
    · have hpzero : p = 0 := by simp only [p, hk, Nat.cast_zero, mul_zero]
      rw [hpzero, zero_add] at haeq
      rw [haeq] at hb ⊢
      exact hres b hb
    · have hdp : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
      have hplim : Order.IsSuccLimit p := Ordinal.isSuccLimit_mul_left
        (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hdp))
        (by exact_mod_cast Nat.pos_of_ne_zero hk)
      have hpowstep : Ordinal.omega0 ^ (d : Ordinal) < Ordinal.omega0 ^ ((d : Ordinal) + 1) :=
        (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (Order.lt_add_one_iff.mpr le_rfl)
      have hbound : r < Ordinal.omega0 ^ ((d : Ordinal) + 1) := hrbound.trans hpowstep
      have hdiv : Ordinal.omega0 ^ (d : Ordinal) ∣ p := dvd_mul_right _ _
      have hnorm := (actualDivisiblePrefixNormAddition p r hp.1 hreps _ hdiv hbound).2
      have hbp : actualOrdinalNorm p ≤ b := by rw [haeq, hnorm] at hb; omega
      have hbr : actualOrdinalNorm r ≤ b - actualOrdinalNorm p := by rw [haeq, hnorm] at hb; omega
      have hs1 := actualConstantBudgetPrefixCountDecomposition b p r hp.1 hreps hplim
        (d : Ordinal) hdp hp.2.2 hbound hbp
      have hs2 := actualConstantBudgetPrefixCountDecomposition (b + restrictedPartitionPeriod (d + 1) m)
        p r hp.1 hreps hplim (d : Ordinal) hdp hp.2.2 hbound (by omega)
      have hmodr := hres (b - actualOrdinalNorm p) hbr
      have hdiff : b + restrictedPartitionPeriod (d + 1) m - actualOrdinalNorm p =
          (b - actualOrdinalNorm p) + restrictedPartitionPeriod (d + 1) m := by omega
      rw [← hdiff] at hmodr
      have hmass : (d + 1) * k ≤ b := by rw [hp.2.1] at hbp; exact hbp
      have hmodp : Nat.ModEq m
          (actualControlledCount (fun _ => b + restrictedPartitionPeriod (d + 1) m) p)
          (actualControlledCount (fun _ => b) p) := by
        rw [actualConstantBudgetMonomialCount d k _ hd (by omega),
          actualConstantBudgetMonomialCount d k _ hd hmass]
        apply modEq_cut_sum
        intro j hj
        have hjb : (d + 1) * j ≤ b := (Nat.mul_le_mul_left (d + 1) hj.le).trans hmass
        have hsub : b + restrictedPartitionPeriod (d + 1) m - (d + 1) * j =
            (b - (d + 1) * j) + restrictedPartitionPeriod (d + 1) m := by omega
        rw [hsub, hK]
        exact restrictedPartitionPeriodMultiple d m _ K hd hm
      rw [haeq, hs1, hs2]
      exact hmodr.add hmodp

end LogicLineages.OrdinalComparison
