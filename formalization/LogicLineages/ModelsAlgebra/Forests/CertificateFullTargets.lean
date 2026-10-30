module

public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchTargets

/-! Full semantic and effective source contract for paper03 prop:certificate.
The search, finite verifier and host list are the literal existing algorithms;
no decision procedure or correctness supplier is a hypothesis. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def FullNegativeCertificateSearch : Prop :=
  CertificateCodecFaithful ∧ CertificateFamilyValidation ∧
    CertificateVerification ∧ CertificateSearchOutputSound ∧
    CertificateExistence ∧ CertificateSearchDomain ∧
    CertificateInvalidInputRejected ∧
    CertificateFiniteOperationsPrimitiveRecursive ∧ CertificateSearchPartialRecursive

end LogicLineages.ModelsAlgebra.Forests.Targets
