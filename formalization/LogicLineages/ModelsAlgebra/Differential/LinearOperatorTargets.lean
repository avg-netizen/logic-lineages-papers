module

public import LogicLineages.ModelsAlgebra.Differential.LinearOperatorDefinitions

@[expose] public section

/-! Fixed direct suppliers for source equation (D-lambda_i)L_i(a)=f(D)a=0
and the ensuing jet reconstruction in paper 15 lem:genericjets/thm:spectral.
No coordinate eigenvalue equation, polynomial-composition theorem or
Vandermonde correctness premise is supplied. This is a constant-base component;
the ordinary-derivation/splitting-extension bridge remains required separately.
-/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def linearOperatorLiteralEvaluation : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (p : Polynomial K) (a : F),
    LinearOperator.applyOperator D p a =
      ∑ k ∈ p.support, p.coeff k • ((D : F → F)^[k]) a

def linearOperatorComposition : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (p q : Polynomial K) (a : F),
    LinearOperator.applyOperator D (p * q) a =
      LinearOperator.applyOperator D p (LinearOperator.applyOperator D q a)

def linearOperatorSourceEquation : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℚ F F)
    (p : Polynomial ℚ) (a : F),
    jetEval D a (LinearOperator.linearEquation p) = LinearOperator.applyOperator D p a

def linearOperatorFactor : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (c : K) (a : F),
    LinearOperator.applyOperator D (Polynomial.X - Polynomial.C c) a = D a - c • a

def linearOperatorSpectralCoordinates : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (a : F),
    LinearOperator.applyOperator D (∏ j : Fin n, (Polynomial.X - Polynomial.C (root j))) a = 0 →
    ∀ i : Fin n, D (LinearOperator.coordinate D root i a) =
      root i • LinearOperator.coordinate D root i a

end LogicLineages.ModelsAlgebra.Differential.Targets
