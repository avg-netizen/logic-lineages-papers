module
public import LogicLineages.CartierObserverCurrent.InitialPrincipalPartsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.InitialPrincipalParts.StatementChecks
theorem fixed_sourceDivisibility : Targets.SourceDivisibility := sourceDivisibility
theorem fixed_boundedPresentation : Targets.BoundedPresentation := boundedPresentation
theorem fixed_fullUniqueness : Targets.FullUniqueness := fullUniqueness
theorem fixed_properCoverage : Targets.ProperCoverage := properCoverage
theorem fixed_initialSourceCoverage : Targets.InitialSourceCoverage := initialSourceCoverage
#audit_namespace LogicLineages.CartierObserverCurrent.InitialPrincipalParts.StatementChecks
end LogicLineages.CartierObserverCurrent.InitialPrincipalParts.StatementChecks
