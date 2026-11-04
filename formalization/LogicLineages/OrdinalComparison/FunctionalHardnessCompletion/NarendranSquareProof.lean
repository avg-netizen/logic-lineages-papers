module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.NarendranQuotientProof
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran.Proof
open Polynomial

theorem division_first_derivative (a b : ZPolynomial) (c : Int)
    (h : (X-1)*b = a-C c) : b.eval 1 = a.derivative.eval 1 := by
  have he := congrArg (fun p : ZPolynomial => p.derivative.eval 1) h
  simpa [Polynomial.derivative_mul] using he

theorem division_second_derivative (a b : ZPolynomial) (c : Int)
    (h : (X-1)*b = a-C c) :
    (2 : Int)*b.derivative.eval 1 = a.derivative.derivative.eval 1 := by
  have he := congrArg (fun p : ZPolynomial => p.derivative.derivative.eval 1) h
  simpa [Polynomial.derivative_mul, two_mul] using he

theorem power_first_moment (n : Nat) (a : NPolynomial)
    (h : (X-1)*signed a = (X : ZPolynomial)^n-1) : a.eval (1 : Nat) = n := by
  have hd := division_first_derivative ((X : ZPolynomial)^n) (signed a) 1 (by simpa using h)
  have he : ((a.eval (1 : Nat) : Nat) : Int) = (n : Int) := by
    simpa [Polynomial.derivative_X_pow] using hd
  exact_mod_cast he

theorem power_second_moment (n : Nat) (a b : NPolynomial)
    (h1 : (X-1)*signed a = (X : ZPolynomial)^n-1)
    (h2 : (X-1)*signed b = signed a-C (n : Int)) :
    2*b.eval (1 : Nat)+n = n^2 := by
  have hd1 := division_second_derivative ((X : ZPolynomial)^n) (signed a) 1 (by simpa using h1)
  have hd2 := division_first_derivative (signed a) (signed b) (n : Int) h2
  have he : (2 : Int)*((b.eval (1 : Nat) : Nat) : Int) = (n : Int)*((n-1 : Nat) : Int) := by
    rw [← hd2, signed_eval_one] at hd1
    simpa [Polynomial.derivative_X_pow, Polynomial.derivative_C_mul] using hd1
  have hnat : 2*b.eval (1 : Nat) = n*(n-1) := by exact_mod_cast he
  rw [hnat]
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring

theorem exactSquareGadget : Targets.ExactSquareGadget := by
  intro u v
  constructor
  · rintro ⟨w,h1,h2,h3⟩
    have hz : (w 3).eval (1 : Nat) = 1 := by
      have he := congrArg (fun p : ZPolynomial => p.eval 1) h1
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_one, sub_self, zero_mul, signed_eval_one] at he
      omega
    obtain ⟨n,hn⟩ := eval_one_eq_one_monomial (w 3) hz
    have h1' : (X-1)*signed (w 0) = (X : ZPolynomial)^n-1 := by
      simpa only [hn, signed_X_pow] using h1
    have ha := power_first_moment n (w 0) h1'
    have hau : (w 0).eval (1 : Nat) = u := by
      have he := congrArg (fun p : ZPolynomial => p.eval 1) h2
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_C, sub_self, zero_mul, signed_eval_one] at he
      omega
    have hv : (w 1).eval (1 : Nat) = v := by
      have he := congrArg (fun p : ZPolynomial => p.eval 1) h3
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_C, sub_self, zero_mul, signed_eval_one] at he
      omega
    have hnu : n = u := ha.symm.trans hau
    have hm := power_second_moment n (w 0) (w 1) h1' (by simpa only [hnu] using h2)
    simpa only [hnu,hv] using hm
  · intro huv
    let z : NPolynomial := X^u
    let a := differenceQuotient z
    let b := differenceQuotient a
    let c := differenceQuotient b
    have h1 : (X-1)*signed a = signed z-1 := by
      simpa [z,a] using nonnegativeQuotientIdentity z
    have ha : a.eval (1 : Nat) = u :=
      power_first_moment u a (by simpa only [z,signed_X_pow] using h1)
    have h2 : (X-1)*signed b = signed a-C (u : Int) := by
      simpa only [ha] using nonnegativeQuotientIdentity a
    have hm := power_second_moment u a b (by simpa only [z,signed_X_pow] using h1) h2
    have hb : b.eval (1 : Nat) = v := by omega
    have h3 : (X-1)*signed c = signed b-C (v : Int) := by
      simpa only [hb] using nonnegativeQuotientIdentity b
    let w : Fin 4 → NPolynomial := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => z)))
    refine ⟨w, ?_⟩
    change (X-1)*signed a=signed z-1 ∧
      (X-1)*signed b=signed a-C (u : Int) ∧
      (X-1)*signed c=signed b-C (v : Int)
    exact ⟨h1,h2,h3⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran.Proof
