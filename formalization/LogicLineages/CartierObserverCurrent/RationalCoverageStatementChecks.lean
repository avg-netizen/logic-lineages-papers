module
public import LogicLineages.CartierObserverCurrent.RationalCoverageProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RationalCoverage.StatementChecks

theorem fixed_statePresentation : Targets.StatePresentation :=
  LogicLineages.CartierObserverCurrent.RationalCoverage.statePresentation

theorem fixed_numeratorDegree : Targets.NumeratorDegree :=
  LogicLineages.CartierObserverCurrent.RationalCoverage.numeratorDegree

theorem fixed_numeratorEvaluation : Targets.NumeratorEvaluation :=
  LogicLineages.CartierObserverCurrent.RationalCoverage.numeratorEvaluation

theorem fixed_actualPartialFraction : Targets.ActualPartialFraction :=
  LogicLineages.CartierObserverCurrent.RationalCoverage.actualPartialFraction

theorem fixed_reconstructionInjective : Targets.ReconstructionInjective :=
  LogicLineages.CartierObserverCurrent.RationalCoverage.reconstructionInjective

theorem fixed_reconstructionCoverage : Targets.ReconstructionCoverage :=
  LogicLineages.CartierObserverCurrent.RationalCoverage.reconstructionCoverage

#audit_namespace LogicLineages.CartierObserverCurrent.RationalCoverage.StatementChecks
end LogicLineages.CartierObserverCurrent.RationalCoverage.StatementChecks
