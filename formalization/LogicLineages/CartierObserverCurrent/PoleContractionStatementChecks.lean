module
public import LogicLineages.CartierObserverCurrent.PoleContractionProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PoleContraction.StatementChecks

theorem fixed_actualRootFactorization : Targets.ActualRootFactorization.{u} :=
  LogicLineages.CartierObserverCurrent.PoleContraction.actualRootFactorization

theorem fixed_fractionPoleContraction : Targets.FractionPoleContraction.{u} :=
  LogicLineages.CartierObserverCurrent.PoleContraction.fractionPoleContraction

theorem fixed_canonicalPoleContraction : Targets.CanonicalPoleContraction.{u} :=
  LogicLineages.CartierObserverCurrent.PoleContraction.canonicalPoleContraction

theorem fixed_noNewPole : Targets.NoNewPole.{u} :=
  LogicLineages.CartierObserverCurrent.PoleContraction.noNewPole

#audit_namespace LogicLineages.CartierObserverCurrent.PoleContraction.StatementChecks
end LogicLineages.CartierObserverCurrent.PoleContraction.StatementChecks
