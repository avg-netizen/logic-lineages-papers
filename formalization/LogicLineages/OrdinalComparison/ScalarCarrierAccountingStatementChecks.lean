module
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingTargets
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.StatementChecks
theorem accounting_origin : Targets.AccountingOrigin := Proof.accountingOrigin
theorem exact_accounting : Targets.ExactAccounting := Proof.exactAccounting
theorem actual_source_accounting : Targets.ActualSourceAccounting := Proof.actualSourceAccounting
end LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting
