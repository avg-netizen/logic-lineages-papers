module

public import LogicLineages.ModelsAlgebra.Differential.CurveDefinitions
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section

/-! Independent comparators for paper 15 `lem:genericcurve`, lines 164–182.
The outer/Z specialization p.eval 0 is the actual rational polynomial
p(Y,0). The first statement requests one small-universe differential-field
witness for each p, uniform over all nonzero rational q. The second states
the literal source avoidance conclusion for each specified q.

Only irreducibility, positive Z-degree, and p(Y,0) ≠ 0 are inputs.
The field, ordinary derivation, transcendental/nonconstant root, and
avoidance are constructed, not assumed. A quotient over Q(Y) is a valid
concrete realization of this existential claim; no model-presentation
isomorphism or full constraint criterion is asserted. Written before proof.
-/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

def genericCurveUniformWitness : Prop :=
  ∀ p : BivariatePolynomial, Irreducible p → 0 < p.natDegree → p.eval 0 ≠ 0 →
    ∃ (F : Type) (fieldF : Field F),
      letI : Field F := fieldF
      ∃ charF : CharZero F,
        letI : CharZero F := charF
        ∃ (D : Derivation ℤ F F) (a : F),
          Transcendental ℚ a ∧ D a ≠ 0 ∧ pairEval a (D a) p = 0 ∧
            ∀ q : Polynomial ℚ, q ≠ 0 → Polynomial.aeval a q ≠ 0

def genericCurveAvoidance : Prop :=
  ∀ (p : BivariatePolynomial), Irreducible p → 0 < p.natDegree → p.eval 0 ≠ 0 →
    ∀ (q : Polynomial ℚ), q ≠ 0 →
      ∃ (F : Type) (fieldF : Field F),
        letI : Field F := fieldF
        ∃ charF : CharZero F,
          letI : CharZero F := charF
          ∃ (D : Derivation ℤ F F) (a : F),
            D a ≠ 0 ∧ pairEval a (D a) p = 0 ∧ Polynomial.aeval a q ≠ 0

end LogicLineages.ModelsAlgebra.Differential.Targets
