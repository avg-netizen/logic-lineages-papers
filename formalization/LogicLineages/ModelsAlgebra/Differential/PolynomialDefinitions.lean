module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-!
# Differential-polynomial syntax and actual jet semantics

This semantic module contains no project implementation theorem. Fixed
comparators can use actual polynomial derivation and jet evaluation
without importing the candidate commutation proof.
-/

namespace LogicLineages.ModelsAlgebra.Differential

abbrev DifferentialPolynomial := MvPolynomial ℕ ℚ

noncomputable def polynomialDerivation :
    Derivation ℚ DifferentialPolynomial DifferentialPolynomial :=
  MvPolynomial.mkDerivation ℚ (fun n : ℕ => MvPolynomial.X (n + 1))

variable {F : Type*} [Field F] [CharZero F]

def jet (D : Derivation ℚ F F) (a : F) : ℕ → F
  | 0 => a
  | n + 1 => D (jet D a n)

noncomputable def jetEval (D : Derivation ℚ F F) (a : F) : DifferentialPolynomial →ₐ[ℚ] F :=
  MvPolynomial.aeval (jet D a)

end LogicLineages.ModelsAlgebra.Differential
