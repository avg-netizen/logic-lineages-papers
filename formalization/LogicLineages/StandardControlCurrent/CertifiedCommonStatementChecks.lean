module
public import LogicLineages.StandardControlCurrent.CertifiedCommonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CertifiedCommonStatementChecks

theorem exactPointwise : CertifiedCommonTargets.ExactPointwise :=
  CertifiedCommonProof.exactPointwise

theorem exactTranslation : CertifiedCommonTargets.ExactTranslation :=
  CertifiedCommonProof.exactTranslation

theorem actualClosedAnswer : CertifiedCommonTargets.ActualClosedAnswer :=
  CertifiedCommonProof.actualClosedAnswer

theorem fullCommonHeadLayers : CertifiedCommonTargets.FullCommonHeadLayers :=
  CertifiedCommonProof.fullCommonHeadLayers

#print axioms exactPointwise
#print axioms exactTranslation
#print axioms actualClosedAnswer
#print axioms fullCommonHeadLayers
end LogicLineages.StandardControlCurrent.CertifiedCommonStatementChecks
#audit_namespace LogicLineages.StandardControlCurrent.CertifiedCommonStatementChecks
