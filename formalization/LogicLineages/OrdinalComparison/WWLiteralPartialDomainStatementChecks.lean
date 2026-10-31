module
public import LogicLineages.OrdinalComparison.WWLiteralPartialDomainProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLiteralPartialDomain : Source.Targets.ActualLiteralPartialDomain :=
  Source.LiteralPartialDomain.actualLiteralPartialDomain

theorem fixed_actualLiteralPartialUniqueBound : Source.Targets.ActualLiteralPartialUniqueBound :=
  Source.LiteralPartialDomain.actualLiteralPartialUniqueBound

theorem fixed_actualRepairedFiniteExpansion : Source.Targets.ActualRepairedFiniteExpansion :=
  Source.LiteralPartialDomain.actualRepairedFiniteExpansion

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
