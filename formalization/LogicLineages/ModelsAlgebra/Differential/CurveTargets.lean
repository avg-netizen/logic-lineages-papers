module

public import LogicLineages.ModelsAlgebra.Differential.CurveDefinitions
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section

/-!
Independent source comparators for the evaluation-kernel and separant steps
of paper 15, proof of `lem:curve` (paper.tex lines 133–149). The degree is
outer/Z degree. No primitive-content assumption, irreducibility over Q(Y),
minimal-polynomial identification, or separant nonvanishing is supplied.
The arbitrary test polynomial q need not be primitive or nonzero.

The ordinary-derivation form derives transcendence from D a ≠ 0 rather than
assuming genericity. These obligations do not yet establish the second-jet
formula, generated-field identification, or designated-root isomorphism.
Written before the external curve-kernel candidate.
-/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def curveEvaluationKernel : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p : BivariatePolynomial) (a b : F),
    Irreducible p → 0 < p.natDegree → Transcendental ℚ a → pairEval a b p = 0 →
    ∀ q : BivariatePolynomial, pairEval a b q = 0 ↔ p ∣ q

def curveSeparantNonzero : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (p : BivariatePolynomial) (a b : F),
    Irreducible p → 0 < p.natDegree → Transcendental ℚ a → pairEval a b p = 0 →
    pairEval a b (separant p) ≠ 0

def ordinaryCurveKernelAndSeparant : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℤ F F)
    (p : BivariatePolynomial) (a : F),
    Irreducible p → 0 < p.natDegree → D a ≠ 0 → pairEval a (D a) p = 0 →
    (∀ q : BivariatePolynomial, pairEval a (D a) q = 0 ↔ p ∣ q) ∧
      pairEval a (D a) (separant p) ≠ 0

end LogicLineages.ModelsAlgebra.Differential.Targets
