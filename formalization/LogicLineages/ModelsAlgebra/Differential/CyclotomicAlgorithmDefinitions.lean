module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicFamilyDefinitions
public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmDefinitions

@[expose] public section

/-! Uniform finite rational inputs for the source unbounded-order family.
The list contains exactly ell coefficients equal to one. No roots, field
presentations, primality oracle or chosen coefficient supplier is input. -/
namespace LogicLineages.ModelsAlgebra.Differential.CyclotomicAlgorithm

abbrev Input := ℕ × ℕ × DensePolynomial.Code

def coefficients (ℓ : ℕ) : DensePolynomial.Code := List.replicate ℓ RationalCode.one

def input (t : Input) : SpectralAlgorithm.Input := (coefficients t.1, t.2.1, t.2.2)

def search (t : Input) : Part Bool := SpectralAlgorithm.search (input t)

end LogicLineages.ModelsAlgebra.Differential.CyclotomicAlgorithm
