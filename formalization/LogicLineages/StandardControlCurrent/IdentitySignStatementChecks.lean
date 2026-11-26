module
public import LogicLineages.StandardControlCurrent.IdentitySignProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.IdentitySignStatementChecks

theorem fixed_identityNormalForm : IdentitySignTargets.IdentityNormalForm := identityNormalForm
theorem fixed_eventualSigns : IdentitySignTargets.EventualSigns := eventualSigns

#print axioms fixed_identityNormalForm
#print axioms fixed_eventualSigns
end LogicLineages.StandardControlCurrent.IdentitySignStatementChecks
