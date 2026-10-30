module

public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm
public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmEffectivity

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm

universe u

theorem computable_realization : Targets.spectralAlgorithmComputableRealization.{u} := by
  let f : Input → Bool := fun t => (search t).get (search_total t)
  have hf : Computable f :=
    Partrec.of_eq_tot search_partial_recursive (fun t => Part.get_mem (search_total t))
  exact ⟨f, hf, fun t => Part.get_mem (search_total t),
    fun t hp => search_correct t (f t) hp (Part.get_mem (search_total t))⟩

end LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm
