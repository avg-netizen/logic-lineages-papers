module
public import LogicLineages.PermittedControl.LiteralFinitenessTargets
public import LogicLineages.OrdinalComparison.WWLiteralPartialDomainProof
public import LogicLineages.StandardControlCurrent.PolicyPartialStatementChecks
public import LogicLineages.StandardControlCurrent.PolicyAbstractionStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_fullLiteralFiniteness : LiteralFinitenessTargets.FullLiteralFiniteness := by
  have hp := StandardControlCurrent.PolicyPartialStatementChecks.full
  have hd := StandardControlCurrent.PolicyAbstractionStatementChecks.full
  exact ⟨OrdinalComparison.Source.LiteralPartialDomain.actualLiteralPartialDomain,
    OrdinalComparison.Source.LiteralPartialDomain.actualLiteralPartialUniqueBound,
    hp.1, hp.2.1, hp.2.2, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩

#print axioms fixed_fullLiteralFiniteness
end LogicLineages.PermittedControl.StatementChecks
