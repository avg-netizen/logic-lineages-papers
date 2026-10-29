module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialDefinitions

@[expose] public section

/-!
# The differential-polynomial ring and actual jet evaluation

The polynomial ring is the free commutative rational algebra in the
variables Y₀,Y₁,... . Its derivation sends Yᵢ to Yᵢ₊₁. Evaluation sends
Yᵢ to the i-th derivative of one actual field element. The commuting
evaluation theorem is proved, not supplied as an interface assumption.
-/

namespace LogicLineages.ModelsAlgebra.Differential

@[simp] theorem polynomialDerivation_X (n : ℕ) :
    polynomialDerivation (MvPolynomial.X n) = MvPolynomial.X (n + 1) :=
  MvPolynomial.mkDerivation_X ℚ _ n

@[simp] theorem polynomialDerivation_C (c : ℚ) :
    polynomialDerivation (MvPolynomial.C c) = 0 :=
  polynomialDerivation.map_algebraMap c

variable {F : Type*} [Field F] [CharZero F]

@[simp] theorem jet_zero (D : Derivation ℚ F F) (a : F) : jet D a 0 = a := rfl

@[simp] theorem jet_succ (D : Derivation ℚ F F) (a : F) (n : ℕ) :
    jet D a (n + 1) = D (jet D a n) := rfl

@[simp] theorem jetEval_X (D : Derivation ℚ F F) (a : F) (n : ℕ) :
    jetEval D a (MvPolynomial.X n) = jet D a n :=
  MvPolynomial.aeval_X _ n

@[simp] theorem jetEval_C (D : Derivation ℚ F F) (a : F) (c : ℚ) :
    jetEval D a (MvPolynomial.C c) = algebraMap ℚ F c :=
  MvPolynomial.aeval_C _ c

/-- Evaluation in a differential field commutes with the constructed
formal derivation on rational differential polynomials. -/
theorem jetEval_polynomialDerivation (D : Derivation ℚ F F) (a : F)
    (p : DifferentialPolynomial) :
    jetEval D a (polynomialDerivation p) = D (jetEval D a p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [polynomialDerivation_C, map_zero, jetEval_C, D.map_algebraMap]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p n hp =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        polynomialDerivation_X, jetEval_X, hp, jet_succ]

end LogicLineages.ModelsAlgebra.Differential
