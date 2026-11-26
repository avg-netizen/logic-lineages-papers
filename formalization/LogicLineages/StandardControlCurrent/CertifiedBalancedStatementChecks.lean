module
public import LogicLineages.StandardControlCurrent.CertifiedBalancedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CertifiedBalancedStatementChecks

theorem lowerCertificateClosure : CertifiedBalancedTargets.LowerCertificateClosure :=
  CertifiedBalancedProof.lowerCertificateClosure

theorem exactPointwise : CertifiedBalancedTargets.ExactPointwise :=
  CertifiedBalancedProof.exactPointwise

theorem exactTranslation : CertifiedBalancedTargets.ExactTranslation :=
  CertifiedBalancedProof.exactTranslation

theorem actualClosedAnswer : CertifiedBalancedTargets.ActualClosedAnswer :=
  CertifiedBalancedProof.actualClosedAnswer

theorem fullBalancedComparison : CertifiedBalancedTargets.FullBalancedComparison :=
  CertifiedBalancedProof.fullBalancedComparison

#print axioms lowerCertificateClosure
#print axioms exactPointwise
#print axioms exactTranslation
#print axioms actualClosedAnswer
#print axioms fullBalancedComparison
end LogicLineages.StandardControlCurrent.CertifiedBalancedStatementChecks
#audit_namespace LogicLineages.StandardControlCurrent.CertifiedBalancedStatementChecks
