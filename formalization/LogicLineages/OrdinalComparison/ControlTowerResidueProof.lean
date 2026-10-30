module
public import LogicLineages.OrdinalComparison.ControlResidueTargets
public import LogicLineages.OrdinalComparison.Control
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem coprime_power_mod_totient (x b e : Nat) (hco : Nat.Coprime x b) :
    Nat.ModEq b (x ^ e) (x ^ (e % b.totient)) := by
  have hEuler := Nat.ModEq.pow_totient hco
  have hbase : Nat.ModEq b (x ^ (e % b.totient)) (x ^ (e % b.totient)) := Nat.ModEq.refl _
  have h := hbase.mul (hEuler.pow (e / b.totient))
  simpa only [← pow_mul, ← pow_add, Nat.mod_add_div, one_pow, mul_one] using h

private theorem coprime_exponent_congruence (x b e e' : Nat) (hco : Nat.Coprime x b)
    (he : Nat.ModEq b.totient e e') : Nat.ModEq b (x ^ e) (x ^ e') := by
  have hx := coprime_power_mod_totient x b e hco
  have hy := coprime_power_mod_totient x b e' hco
  have hmod : e % b.totient = e' % b.totient := he
  rw [hmod] at hx
  exact hx.trans hy.symm

/-- Genuine tower stabilization by induction on the integer modulus. -/
theorem exponentTowerResidueStability : Targets.ExponentTowerResidueStability := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm n n' k k' hn hn' hk hk'
    by_cases hm1 : m = 1
    · subst m
      exact Nat.modEq_one
    · have hm2 : 1 < m := by omega
      obtain ⟨a, b, hbodd, hmEq⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hm)
      have hbpos : 0 < b := by
        obtain ⟨v, hv⟩ := hbodd
        omega
      have hpowpos : 0 < 2 ^ a := Nat.pow_pos (by decide)
      have hbm : b ≤ m := by
        rw [hmEq]
        exact Nat.le_mul_of_pos_left _ hpowpos
      have ham : a ≤ m := by
        have hpow : 2 ^ a ≤ m := by
          rw [hmEq]
          exact Nat.le_mul_of_pos_right _ hbpos
        exact Nat.lt_two_pow_self.le.trans hpow
      have hco : Nat.Coprime 2 b := hbodd.coprime_two_left
      cases k with
      | zero => omega
      | succ k =>
        cases k' with
        | zero => omega
        | succ k' =>
          let e := ((fastControl 0)^[k]) n
          let e' := ((fastControl 0)^[k']) n'
          have hnE : n ≤ e := iterate_self_le (fun z => (self_lt_fastControl 0 z).le) k n
          have hnE' : n' ≤ e' := iterate_self_le (fun z => (self_lt_fastControl 0 z).le) k' n'
          have haE : a ≤ e := ham.trans (hn.trans hnE)
          have haE' : a ≤ e' := ham.trans (hn'.trans hnE')
          have htwo : Nat.ModEq (2 ^ a) (2 ^ e) (2 ^ e') :=
            (Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 haE)).trans
              (Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 haE')).symm
          have hodd : Nat.ModEq b (2 ^ e) (2 ^ e') := by
            by_cases hb1 : b = 1
            · subst b
              exact Nat.modEq_one
            · have hb2 : 1 < b := by omega
              have hq : b.totient < m := (Nat.totient_lt b hb2).trans_le hbm
              have hqpos : 0 < b.totient := Nat.totient_pos.mpr hbpos
              have hqk : b.totient ≤ k := by omega
              have hqk' : b.totient ≤ k' := by omega
              have hexp := ih b.totient hq hqpos n n' k k'
                (hq.le.trans hn) (hq.le.trans hn') hqk hqk'
              exact coprime_exponent_congruence 2 b e e' hco hexp
          have hfull : Nat.ModEq (2 ^ a * b) (2 ^ e) (2 ^ e') :=
            (Nat.modEq_and_modEq_iff_modEq_mul (hco.pow_left a)).mp ⟨htwo, hodd⟩
          rw [← hmEq] at hfull
          simpa only [e, e', Function.iterate_succ_apply', fastControl] using hfull

end LogicLineages.OrdinalComparison
