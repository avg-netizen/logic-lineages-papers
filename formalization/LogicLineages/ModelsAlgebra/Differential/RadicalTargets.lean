module

public import LogicLineages.ModelsAlgebra.Differential.RadicalDefinitions
public import LogicLineages.ModelsAlgebra.Differential.CurveDefinitions
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

/-! Independent suppliers for paper 15's order-one constant-exception
argument, paper.tex lines 186–203. Root quantification uses the actual
algebraic closure, while the ambient-field implication explicitly covers
arbitrary characteristic-zero extensions. No root-existence oracle,
q-primitivity, or radical/root criterion is supplied as a premise.
The bad constant is equipped with the actual zero ordinary derivation.
Written before proof; neither constrainedness nor an algorithm is defined
by the divisibility criterion. -/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def rationalRadicalMonicSquarefree : Prop :=
  ∀ r : Polynomial ℚ, r ≠ 0 → (rationalRadical r).Monic ∧ Squarefree (rationalRadical r)

def rationalRadicalRootCriterion : Prop :=
  ∀ (r q : Polynomial ℚ), r ≠ 0 →
    (rationalRadical r ∣ q ↔ ∀ c : AlgebraicClosure ℚ,
      Polynomial.aeval c r = 0 → Polynomial.aeval c q = 0)

def radicalAmbientRootVanishing : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (r q : Polynomial ℚ) (c : F),
    r ≠ 0 → rationalRadical r ∣ q → Polynomial.aeval c r = 0 → Polynomial.aeval c q = 0

def badConstantCurveWitness : Prop :=
  ∀ (p : BivariatePolynomial) (q : Polynomial ℚ), p.eval 0 ≠ 0 →
    ¬rationalRadical (p.eval 0) ∣ q →
    ∃ c : AlgebraicClosure ℚ,
      pairEval c ((0 : Derivation ℤ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) c) p = 0 ∧
      Polynomial.aeval c q ≠ 0

end LogicLineages.ModelsAlgebra.Differential.Targets
