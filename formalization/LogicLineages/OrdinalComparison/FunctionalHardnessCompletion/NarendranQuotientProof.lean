module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.NarendranTargets
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Tactic.Ring
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran.Proof
open Polynomial

@[simp] theorem signed_add (p q : NPolynomial) : signed (p+q) = signed p+signed q := by
  simp [signed]
@[simp] theorem signed_mul (p q : NPolynomial) : signed (p*q) = signed p*signed q := by
  simp [signed]
@[simp] theorem signed_C (n : Nat) : signed (C n) = C (n : Int) := by
  simp [signed]
@[simp] theorem signed_X_pow (n : Nat) : signed (X^n) = (X : ZPolynomial)^n := by
  simp [signed]
@[simp] theorem signed_eval_one (p : NPolynomial) :
    (signed p).eval (1 : Int) = ((p.eval (1 : Nat) : Nat) : Int) := by
  simpa [signed] using Polynomial.eval_map_apply (p:=p) (Nat.castRingHom Int) (1 : Nat)

theorem geometric_mul (n : Nat) : (X-1)*signed (geometric n) = (X : ZPolynomial)^n-1 := by
  induction n with
  | zero => simp [geometric, signed]
  | succ n ih =>
      have hg : geometric (n+1) = geometric n + (X : NPolynomial)^n := by
        simp only [geometric, Finset.sum_range_succ]
      rw [hg, signed_add, mul_add, ih, signed_X_pow, pow_succ]
      ring

theorem quotient_add (p q : NPolynomial) :
    differenceQuotient (p+q) = differenceQuotient p+differenceQuotient q := by
  apply Polynomial.sum_add_index
  · intro n
    simp
  · intro n a b
    simp [add_mul]

theorem quotient_monomial (n c : Nat) :
    differenceQuotient (monomial n c) = C c*geometric n := by
  simp [differenceQuotient, Polynomial.sum_monomial_index]

theorem nonnegativeQuotientIdentity : Targets.NonnegativeQuotientIdentity := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [quotient_add, signed_add, mul_add, hp, hq, signed_add,
        Polynomial.eval_add, Nat.cast_add, Polynomial.C_add]
      ring
  | monomial n c =>
      rw [quotient_monomial, signed_mul, signed_C]
      rw [← mul_assoc, mul_comm (X-1) (C (c : Int)), mul_assoc, geometric_mul]
      simp only [signed, Polynomial.map_monomial,
        Polynomial.eval_monomial, one_pow, mul_one]
      change C (c : Int)*((X : ZPolynomial)^n-1) = monomial n (c : Int)-C (c : Int)
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      ring

theorem eval_one_eq_one_monomial (p : NPolynomial) (hp : p.eval (1 : Nat) = 1) :
    ∃ n : Nat, p = (X : NPolynomial)^n := by
  have hs : p.toFinsupp.sum (fun _ c => c) = 1 := by
    simpa only [Polynomial.eval_eq_sum, one_pow, mul_one, Polynomial.sum,
      Finsupp.sum, Polynomial.support, Polynomial.coeff] using hp
  obtain ⟨n, hn⟩ := (Finsupp.sum_eq_one_iff p.toFinsupp).mp hs
  refine ⟨n, ?_⟩
  have he : p = monomial n 1 := by
    apply Polynomial.toFinsupp_injective
    exact hn
  rw [← Polynomial.C_mul_X_pow_eq_monomial] at he
  simpa using he

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran.Proof
