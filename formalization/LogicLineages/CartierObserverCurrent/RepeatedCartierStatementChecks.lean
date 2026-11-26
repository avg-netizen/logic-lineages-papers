module
public import LogicLineages.CartierObserverCurrent.RepeatedCartierProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RepeatedCartier.StatementChecks
theorem fixed_simpleIteration : Targets.SimpleIteration := simpleIteration
theorem fixed_higherVanishing : Targets.HigherVanishing := higherVanishing
theorem fixed_finiteAdditivity : Targets.FiniteAdditivity := finiteAdditivity
theorem fixed_principalReduction : Targets.PrincipalReduction := principalReduction
#audit_namespace LogicLineages.CartierObserverCurrent.RepeatedCartier.StatementChecks
end LogicLineages.CartierObserverCurrent.RepeatedCartier.StatementChecks
