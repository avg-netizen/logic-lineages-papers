module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicAlgorithm

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily

universe u

theorem full_source : Targets.cyclotomicFullSource.{u} :=
  ⟨prime_irreducible, prime_spectral_promise, orders_unbounded, semantic_family,
    CyclotomicAlgorithm.input_coverage, CyclotomicAlgorithm.effective_family⟩

end LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily
