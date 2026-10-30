module

public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem fixed_certificateCodecFaithful : Targets.CertificateCodecFaithful :=
  CertificateSearchProof.certificateCodecFaithful

theorem fixed_certificateFamilyValidation : Targets.CertificateFamilyValidation :=
  CertificateSearchProof.certificateFamilyValidation

theorem fixed_certificateVerification : Targets.CertificateVerification :=
  CertificateSearchProof.certificateVerification

theorem fixed_certificateSearchOutputSound : Targets.CertificateSearchOutputSound :=
  CertificateSearchProof.certificateSearchOutputSound

theorem fixed_certificateExistence : Targets.CertificateExistence :=
  CertificateSearchProof.certificateExistence

theorem fixed_certificateSearchDomain : Targets.CertificateSearchDomain :=
  CertificateSearchProof.certificateSearchDomain

theorem fixed_certificateInvalidInputRejected : Targets.CertificateInvalidInputRejected :=
  CertificateSearchProof.certificateInvalidInputRejected

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
