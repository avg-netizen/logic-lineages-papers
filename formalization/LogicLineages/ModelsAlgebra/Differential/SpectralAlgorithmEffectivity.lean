module

public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmTargets
public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantCodeEffectivity
public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivisionEffectivity
public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision
public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchEffectivity

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm

theorem order_primitive_recursive : Primrec order := by
  have h := PolynomialCertificateSearch.degree_primitive_recursive.comp
    (show Primrec (fun t : Input => t.1) from Primrec.fst)
  exact h.of_eq (fun _ => rfl)

theorem prepare_primitive_recursive : Primrec prepare := by
  have hn := order_primitive_recursive
  have hc := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hn) (Primrec.const 2)
  have hb : Primrec (fun t : Input => t.2.1) := Primrec.fst.comp Primrec.snd
  have hq : Primrec (fun t : Input => t.2.2) := Primrec.snd.comp Primrec.snd
  have hf : Primrec (fun t : Input => t.1) := Primrec.fst
  have hcommon := Primrec.nat_max.comp hc hb
  have hri := hn.pair (hc.pair hf)
  have hr := SpectralResultantCode.obstruction_primitive_recursive.comp hri
  have hrrebase := BoxPolynomialCode.rebase_primitive_recursive.comp
    (hn.pair (hc.pair (hcommon.pair hr)))
  have hqrebase := BoxPolynomialCode.rebase_primitive_recursive.comp
    (hn.pair (hb.pair (hcommon.pair hq)))
  have h := hn.pair (hcommon.pair (hrrebase.pair hqrebase))
  exact h.of_eq (fun _ => rfl)

theorem search_total : Targets.spectralAlgorithmSearchTotal := by
  intro t
  exact BoundedPolynomialDivision.search_total (prepare t)

theorem search_partial_recursive : Targets.spectralAlgorithmSearchPartialRecursive := by
  have h := BoundedPolynomialDivision.search_partial_recursive.comp prepare_primitive_recursive.to_comp
  exact h.of_eq (fun _ => rfl)

end LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm
