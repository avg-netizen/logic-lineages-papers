module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicPromise
public import LogicLineages.ModelsAlgebra.Differential.SpectralConstraint

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily

universe u

theorem semantic_family : Targets.cyclotomicSemanticFamily.{u} := by
  intro ℓ hp
  obtain ⟨hm, _hd, hn, root, hr, hf⟩ := prime_spectral_promise ℓ hp
  obtain ⟨R, _hR, hRzero, hcon, hcrit⟩ :=
    SpectralConstraint.complete (polynomial ℓ) root hm hn hr hf
  exact ⟨R, hRzero, hcon, hcrit⟩

end LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily
