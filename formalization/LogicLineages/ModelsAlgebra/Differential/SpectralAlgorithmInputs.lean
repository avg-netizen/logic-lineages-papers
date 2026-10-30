module

public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmTargets
public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode
public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm

theorem input_coverage : Targets.spectralAlgorithmInputCoverage := by
  intro f q
  obtain ⟨fc, hfc⟩ := DensePolynomial.coverage f
  subst f
  obtain ⟨B, qc, hB, hq⟩ := BoxPolynomialCode.coverage (DensePolynomial.value fc).natDegree q
  exact ⟨fc, B, qc, hB, rfl, hq⟩

theorem order_correct : Targets.spectralAlgorithmOrder := by
  intro t
  exact PolynomialCertificateSearch.degree_correct t.1

end LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm
