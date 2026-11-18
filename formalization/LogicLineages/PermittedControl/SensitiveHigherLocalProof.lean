module
public import LogicLineages.PermittedControl.SensitiveQuadraticAdmissionProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem sensitive_quotient_large (R B t u c p v : Nat) (ht : thickBlockTail R B ≤ t)
    (hu : 2*t+4 ≤ u) (hc : c ≤ R) (hp : p ≤ R) (hv : 0 < v) (hvR : v ≤ R) :
    R+2 < (u-c-p)/v := by
  have ht4 : 100*(R+2)^4 ≤ t := (le_max_left _ _).trans ht
  have hR4 : R+2 ≤ (R+2)^4 := Nat.le_self_pow (by omega : 4 ≠ 0) (R+2)
  have h24 : (R+2)^2 ≤ (R+2)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hprod : (R+3)*v ≤ 2*(R+2)^4 := by
    have h := Nat.mul_le_mul (show R+3 ≤ 2*(R+2) by omega) (show v ≤ R+2 by omega)
    have h' : (R+3)*v ≤ 2*((R+2)^2) := by simpa only [Nat.pow_two,Nat.mul_assoc] using h
    exact h'.trans (Nat.mul_le_mul_left 2 h24)
  have hX : 2*(R+2)^4 ≤ u-c-p := by omega
  have hq : R+3 ≤ (u-c-p)/v := (Nat.le_div_iff_mul_le hv).mpr (hprod.trans hX)
  omega

 theorem limitPart_zero_or_limit (w : Ordinal.{0}) : actualLimitPart w=0 ∨ Order.IsSuccLimit (actualLimitPart w) := by
  by_cases h : w/Ordinal.omega0=0
  · left
    simp [actualLimitPart,h]
  · right
    exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (pos_iff_ne_zero.mpr h)

 theorem local_limit_separation (P a : Ordinal.{0}) (ha : a < epsilonZero)
    (h2 : (2 : Ordinal) ≤ a) (hl : Order.IsSuccLimit a) (X Y : Nat) (hX : 2 ≤ X) (hY : 2 ≤ Y) (hYX : Y < X) :
    actualLimitPart (P+actualMaximumPredecessor (Ordinal.omega0^a) X) ≠
      actualLimitPart (P+actualMaximumPredecessor (Ordinal.omega0^a) Y) := by
  have hpw := phase_power_below a ha
  have hsmall : Ordinal.omega0 < Ordinal.omega0^a := by
    simpa using (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono
      (lt_of_lt_of_le (show (1 : Ordinal.{0})<2 by norm_num) h2)
  have hNW : actualOrdinalNorm Ordinal.omega0=2 := by simpa using actualFiniteHeadNorm 1 0
  have hb : ∀ b : Nat, 2 ≤ b → Ordinal.omega0 ≤ actualMaximumPredecessor (Ordinal.omega0^a) b := by
    intro b hb
    exact (actualMaximumPredecessor_correct _ (Ordinal.opow_pos a Ordinal.omega0_pos) hpw b).2 ⟨hsmall,by rwa [hNW]⟩
  have hbX := (actualMaximumPredecessor_correct _ (Ordinal.opow_pos a Ordinal.omega0_pos) hpw X).1.1.trans hpw
  have hbY := (actualMaximumPredecessor_correct _ (Ordinal.opow_pos a Ordinal.omega0_pos) hpw Y).1.1.trans hpw
  have hlog := (limitLocalTail a ha hl).2 Y X (by omega) hYX
  rw [phase_limit_add P _ hbX (hb X hX),phase_limit_add P _ hbY (hb Y hY)]
  intro heq
  have h := congrArg (Ordinal.log Ordinal.omega0) (add_left_cancel heq)
  rw [← phase_limit_log _ hbX (hb X hX),← phase_limit_log _ hbY (hb Y hY)] at h
  exact (ne_of_lt hlog) h.symm

 theorem absolute_limit_of_relative (mu A : Ordinal.{0}) (hA : A < epsilonZero)
    (hrel : Ordinal.omega0 ≤ A-mu) : actualLimitPart A=mu+actualLimitPart (A-mu) := by
  have hmuA : mu ≤ A := by simpa only [add_zero] using (Ordinal.lt_sub.mp (Ordinal.omega0_pos.trans_le hrel)).le
  have heq := Ordinal.add_sub_cancel_of_le hmuA
  have hb := (Ordinal.sub_le_self A mu).trans_lt hA
  conv_lhs => rw [← heq]
  exact phase_limit_add mu (A-mu) hb hrel

end LogicLineages.PermittedControl
