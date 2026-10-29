module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialDefinitions

@[expose] public section

/-!
Independent acceptance comparator for paper 15's differential-polynomial
semantics (Definitions and algebraic preliminaries, immediately before
`def:constraint`): Q{Y} = Q[Y_0,Y_1,...], DY_i = Y_(i+1), with evaluation
Y_i |-> D^i a in an arbitrary characteristic-zero differential field.

This comparator was added during external continuation before any external
repair of the already existing PolynomialEvaluation candidate, not before
that candidate's original authorship. It imports only the frozen actual
semantic definitions, not the candidate commutation theorem. This supplier
does not assert either full constraint criterion or its effectiveness.
-/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

/-- Actual jet evaluation respects the constructed formal derivation. -/
def jetEvaluationCommutes : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℚ F F)
    (a : F) (p : DifferentialPolynomial),
    jetEval D a (polynomialDerivation p) = D (jetEval D a p)

end LogicLineages.ModelsAlgebra.Differential.Targets
