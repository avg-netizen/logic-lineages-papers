module

public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision
public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivisionEffectivity

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision

theorem computable_realization : Targets.boundedDivisionComputableRealization := by
  let f : Input → Bool := fun t => (search t).get (search_total t)
  have hf : Computable f :=
    Partrec.of_eq_tot search_partial_recursive (fun t => Part.get_mem (search_total t))
  exact ⟨f, hf, fun t => Part.get_mem (search_total t),
    fun n B hB pc qc => search_correct n B hB pc qc (f (n, B, pc, qc))
      (Part.get_mem (search_total (n, B, pc, qc)))⟩

end LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision
