module
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran
open Polynomial
abbrev NPolynomial := Polynomial Nat
abbrev ZPolynomial := Polynomial Int
noncomputable def signed (p : NPolynomial) : ZPolynomial := p.map (Nat.castRingHom Int)

/-- Narendran Lemma 3.5: the unknowns are Y1,Y2,Y3,Z, all in N[X].
The parameters u,v are natural constants, paid separately by the constant
gadget. Every displayed equation is linear in the unknown polynomials. -/
def SquareGadget (u v : Nat) (w : Fin 4 → NPolynomial) : Prop :=
  (X-1)*signed (w 0) = signed (w 3)-1 ∧
  (X-1)*signed (w 1) = signed (w 0)-C (u : Int) ∧
  (X-1)*signed (w 2) = signed (w 1)-C (v : Int)

/-- Narendran Lemma 3.3, univariate instance, with unknowns
U1,U2,U3,W1,W2,Y1,Y2. There is no assumed degree or nonzero restriction. -/
def ConstantGadget (v : NPolynomial) (w : Fin 7 → NPolynomial) : Prop :=
  (X-1)*signed (w 0) = signed (w 3)-1 ∧
  (X^2-1)*signed (w 1) = signed (w 4)-1 ∧
  (X-1)*signed (w 2) = signed (w 1)-signed (w 0) ∧
  (X-2)*signed (w 5) = signed (w 0)-signed v ∧
  (X^2-2)*signed (w 6) = signed (w 1)-signed v

def SimultaneousConstantGadget {n : Nat} (z : Fin n → NPolynomial) : Prop :=
  ∃ (v extra : NPolynomial) (w : Fin 7 → NPolynomial), ConstantGadget v w ∧
    (∑ i : Fin n, z i) + extra = v

/-- Nonnegative divided difference at one. It supplies witnesses without
introducing negative coefficients or assuming polynomial division preserves
nonnegativity. -/
noncomputable def geometric (n : Nat) : NPolynomial :=
  ∑ i ∈ Finset.range n, X^i
noncomputable def differenceQuotient (p : NPolynomial) : NPolynomial :=
  p.sum fun n c => C c * geometric n

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Narendran
