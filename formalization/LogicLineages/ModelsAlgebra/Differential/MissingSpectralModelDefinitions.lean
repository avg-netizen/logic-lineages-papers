module

public import LogicLineages.ModelsAlgebra.Differential.SpectralModelDefinitions
public import LogicLineages.ModelsAlgebra.Differential.HyperplaneDefinitions

@[expose] public section

/-! A literal missing-coordinate solution inside the constructed generic
rational-function differential field. The unused variable may remain in the
ambient field; the designated-root semantics uses its actual generated field. -/
namespace LogicLineages.ModelsAlgebra.Differential.SpectralModel

noncomputable def missingPoint (K : Type*) [Field K] (n : ℕ) (skipped : Fin n) : ModelField K n :=
  ∑ j : Fin n, if j = skipped then 0 else coordinateVariable K n j

end LogicLineages.ModelsAlgebra.Differential.SpectralModel
