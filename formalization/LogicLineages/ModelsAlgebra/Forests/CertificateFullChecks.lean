module

public import LogicLineages.ModelsAlgebra.Forests.CertificateFullTargets
public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchChecks
public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchEffectivityChecks
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

/-- Entire effective negative-certificate source contract, including the
actual finite algorithms and the original mathematical JEP predicate. -/
theorem fixed_fullNegativeCertificateSearch : Targets.FullNegativeCertificateSearch :=
  ⟨fixed_certificateCodecFaithful, fixed_certificateFamilyValidation,
    fixed_certificateVerification, fixed_certificateSearchOutputSound,
    fixed_certificateExistence, fixed_certificateSearchDomain,
    fixed_certificateInvalidInputRejected,
    fixed_certificateFiniteOperationsPrimitiveRecursive,
    fixed_certificateSearchPartialRecursive⟩

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
