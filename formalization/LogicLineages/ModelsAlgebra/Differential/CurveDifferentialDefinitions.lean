module

public import LogicLineages.ModelsAlgebra.Differential.CurveDefinitions
public import LogicLineages.ModelsAlgebra.Differential.GeneratedFieldDefinitions
public import LogicLineages.ModelsAlgebra.Differential.RationalBase
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.Derivation.MapCoeffs

@[expose] public section

/-! Actual Y-partial differentiation on Q[Y][Z] applies the formal
Q[Y] derivative coefficientwise. The first-jet field is the ordinary
intermediate-field adjoin of a and Da, not assumed differentially closed. -/

namespace LogicLineages.ModelsAlgebra.Differential

noncomputable def partialY (p : BivariatePolynomial) : BivariatePolynomial :=
  PolynomialModule.equivPolynomial (Polynomial.derivative'.mapCoeffs p)

variable {F : Type*} [Field F] [CharZero F]

def firstJetField (D : Derivation ℤ F F) (a : F) : IntermediateField ℚ F :=
  IntermediateField.adjoin ℚ ({a, D a} : Set F)

end LogicLineages.ModelsAlgebra.Differential
