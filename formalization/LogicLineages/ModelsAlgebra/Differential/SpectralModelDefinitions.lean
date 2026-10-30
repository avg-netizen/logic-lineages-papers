module

public import LogicLineages.ModelsAlgebra.Differential.FractionField
public import LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinateDefinitions
public import Mathlib.Algebra.MvPolynomial.Derivation

@[expose] public section

/-! The literal rational-function-field construction in paper 15, section
Generic and missing-coordinate solutions. Its derivation is constructed by
the checked fraction-extension graph; no prescribed field-derivation oracle. -/
namespace LogicLineages.ModelsAlgebra.Differential.SpectralModel

variable (K : Type*) [Field K] (n : ℕ)

abbrev CoordinateRing := MvPolynomial (Fin n) K
abbrev ModelField := FractionRing (CoordinateRing K n)

noncomputable def coordinateVariable (i : Fin n) : ModelField K n :=
  algebraMap (CoordinateRing K n) (ModelField K n) (MvPolynomial.X i)

noncomputable def polynomialD (root : Fin n → K) :
    Derivation K (CoordinateRing K n) (ModelField K n) :=
  MvPolynomial.mkDerivation K (fun i => root i • coordinateVariable K n i)

noncomputable def derivation (root : Fin n → K) :
    Derivation K (ModelField K n) (ModelField K n) :=
  FractionField.extension (polynomialD K n root)

noncomputable def point : ModelField K n := ∑ i : Fin n, coordinateVariable K n i

end LogicLineages.ModelsAlgebra.Differential.SpectralModel
