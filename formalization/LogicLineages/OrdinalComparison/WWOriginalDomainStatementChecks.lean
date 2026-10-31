module
public import LogicLineages.OrdinalComparison.WWOriginalDomainProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalFiniteValueCalibration : Source.Targets.OriginalFiniteValueCalibration :=
  Source.OriginalDomain.originalFiniteValueCalibration

theorem fixed_originalClosedScalarFinite : Source.Targets.OriginalClosedScalarFinite :=
  Source.OriginalDomain.originalClosedScalarFinite

theorem fixed_originalAmbientScalarFinite : Source.Targets.OriginalAmbientScalarFinite :=
  Source.OriginalDomain.originalAmbientScalarFinite

theorem fixed_originalAllOneSubstitution : Source.Targets.OriginalAllOneSubstitution :=
  Source.OriginalDomain.originalAllOneSubstitution

theorem fixed_originalHeadOneExtension : Source.Targets.OriginalHeadOneExtension :=
  Source.OriginalDomain.originalHeadOneExtension

theorem fixed_originalHeadAmbientInclusion : Source.Targets.OriginalHeadAmbientInclusion :=
  Source.OriginalDomain.originalHeadAmbientInclusion

theorem fixed_originalHeadLiteralAdmission : Source.Targets.OriginalHeadLiteralAdmission :=
  Source.OriginalDomain.originalHeadLiteralAdmission

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
