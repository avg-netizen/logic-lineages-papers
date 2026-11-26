module
public import LogicLineages.CartierObserverCurrent.ProfileDescentProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileDescent.StatementChecks

theorem fixed_frobeniusTransport : Targets.FrobeniusTransport :=
  LogicLineages.CartierObserverCurrent.ProfileDescent.frobeniusTransport

theorem fixed_compatibilityFixed : Targets.CompatibilityFixed :=
  LogicLineages.CartierObserverCurrent.ProfileDescent.compatibilityFixed

theorem fixed_profileToBase : Targets.ProfileToBase :=
  LogicLineages.CartierObserverCurrent.ProfileDescent.profileToBase

theorem fixed_baseToProfile : Targets.BaseToProfile :=
  LogicLineages.CartierObserverCurrent.ProfileDescent.baseToProfile

#audit_namespace LogicLineages.CartierObserverCurrent.ProfileDescent.StatementChecks
end LogicLineages.CartierObserverCurrent.ProfileDescent.StatementChecks
