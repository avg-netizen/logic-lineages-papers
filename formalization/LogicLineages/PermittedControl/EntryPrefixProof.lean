module
public import LogicLineages.PermittedControl.EntryLinearProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixMaximumProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

theorem square_mul : Ordinal.omega0 ^ (2 : Ordinal.{0}) = Ordinal.omega0 * Ordinal.omega0 := by
  rw [show (2 : Ordinal.{0}) = 1+1 by norm_num, Ordinal.opow_add, Ordinal.opow_one]

theorem square_dvd_omega {P : Ordinal.{0}} (hP : Ordinal.omega0 ^ (2 : Ordinal.{0}) ∣ P) :
    Ordinal.omega0 ∣ P := by
  exact (show Ordinal.omega0 ∣ Ordinal.omega0 ^ (2 : Ordinal.{0}) by rw [square_mul]; exact dvd_mul_right _ _).trans hP

theorem below_square_divisible (r : Ordinal.{0}) (hr : r < Ordinal.omega0 ^ (2 : Ordinal.{0}))
    (hd : Ordinal.omega0 ∣ r) : ∃ j : Nat, r = Ordinal.omega0 * (j : Ordinal) := by
  rw [square_mul] at hr
  obtain ⟨q,hq,s,hs,heq⟩ := Ordinal.lt_mul_iff.mp hr
  obtain ⟨j,rfl⟩ := Ordinal.lt_omega0.mp hq
  have hz := Ordinal.mod_eq_zero_of_dvd hd
  rw [heq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hs] at hz
  exact ⟨j, by simpa only [hz, add_zero] using heq⟩

theorem remainder_divisible (P r : Ordinal.{0}) (hP : Ordinal.omega0 ∣ P)
    (h : Ordinal.omega0 ∣ P+r) : Ordinal.omega0 ∣ r := by
  obtain ⟨q,hq⟩ := hP
  apply Ordinal.dvd_of_mod_eq_zero
  have hz := Ordinal.mod_eq_zero_of_dvd h
  rw [hq, Ordinal.mul_add_mod_self] at hz
  exact hz

theorem target_prefix_decomposition (nu : Ordinal.{0}) (hnu : nu = 0 ∨ Order.IsSuccLimit nu)
    (heps : nu < epsilonZero) :
    ∃ (P : Ordinal.{0}) (j : Nat), P < epsilonZero ∧ Ordinal.omega0 ^ (2 : Ordinal.{0}) ∣ P ∧
      nu = P + Ordinal.omega0 * (j : Ordinal) ∧ actualOrdinalNorm nu = actualOrdinalNorm P + 2*j := by
  let P := Ordinal.omega0 ^ (2 : Ordinal.{0}) * (nu / (Ordinal.omega0 ^ (2 : Ordinal.{0})))
  let r := nu % (Ordinal.omega0 ^ (2 : Ordinal.{0}))
  have hP : P ≤ nu := Ordinal.mul_div_le _ _
  have hdiv : Ordinal.omega0 ^ (2 : Ordinal.{0}) ∣ P := dvd_mul_right _ _
  have heq : nu = P+r := (Ordinal.div_add_mod _ _).symm
  have hr : r < Ordinal.omega0 ^ (2 : Ordinal.{0}) :=
    Ordinal.mod_lt _ (ne_of_gt (Ordinal.opow_pos _ Ordinal.omega0_pos))
  have hrd : Ordinal.omega0 ∣ r := remainder_divisible P r (square_dvd_omega hdiv)
    (by rw [← heq]; exact limit_divisible nu hnu)
  obtain ⟨j,hj⟩ := below_square_divisible r hr hrd
  have hnorm := actualDivisiblePrefixNormAddition P (Ordinal.omega0 * (j : Ordinal))
    (hP.trans_lt heps) (by simpa using finiteCoefficient_below j 0) 1
    (by simpa only [Ordinal.opow_one] using square_dvd_omega hdiv)
    (by simpa only [← hj, show (1 : Ordinal.{0})+1 = 2 by norm_num] using hr)
  refine ⟨P,j,hP.trans_lt heps,hdiv,by rw [heq,hj],?_⟩
  rw [heq,hj,hnorm.2]
  have h := actualFiniteHeadNorm j 0
  simpa only [Nat.cast_zero, add_zero, Nat.add_zero] using congrArg (fun n => actualOrdinalNorm P+n) h

theorem long_interval_above (lam nu P : Ordinal.{0}) (j : Nat)
    (hnu : nu = P+Ordinal.omega0*(j : Ordinal))
    (hP : Ordinal.omega0 ^ (2 : Ordinal.{0}) ∣ P) (hlam : Order.IsSuccLimit lam)
    (hlt : nu < lam)
    (hlong : ¬ ∃ k : Nat, 0 < k ∧ lam = nu+Ordinal.omega0*(k : Ordinal)) :
    P+Ordinal.omega0 ^ (2 : Ordinal.{0}) ≤ lam := by
  by_contra h
  have hltbar : lam < P+Ordinal.omega0 ^ (2 : Ordinal.{0}) := lt_of_not_ge h
  have hPlo : P ≤ lam := (by rw [hnu]; exact le_self_add : P ≤ nu).trans hlt.le
  let r := lam-P
  have heq : lam = P+r := (Ordinal.add_sub_cancel_of_le hPlo).symm
  have hr : r < Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
    apply (add_lt_add_iff_left P).mp
    rwa [← heq]
  have hrd := remainder_divisible P r (square_dvd_omega hP)
    (by rw [← heq]; exact limit_divisible lam (Or.inr hlam))
  obtain ⟨k,hk⟩ := below_square_divisible r hr hrd
  have hjk : j < k := by
    rw [hnu, heq, hk] at hlt
    have ho := (add_lt_add_iff_left P).mp hlt
    have hcoeff := (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.lt_iff_lt.mp ho
    exact_mod_cast hcoeff
  apply hlong
  refine ⟨k-j,by omega,?_⟩
  rw [heq,hk,hnu,add_assoc,← mul_add]
  congr 2
  exact_mod_cast (Nat.add_sub_of_le hjk.le).symm

end LogicLineages.PermittedControl
