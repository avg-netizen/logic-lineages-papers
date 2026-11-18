module
public import LogicLineages.CartierObserverCurrent.SplittingRootsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SplittingRoots.StatementChecks

theorem fixed_finiteFieldAndRoots : Targets.FiniteFieldAndRoots :=
  LogicLineages.CartierObserverCurrent.SplittingRoots.finiteFieldAndRoots

theorem fixed_actualSplitting : Targets.ActualSplitting :=
  LogicLineages.CartierObserverCurrent.SplittingRoots.actualSplitting

theorem fixed_exactAllRoots : Targets.ExactAllRoots :=
  LogicLineages.CartierObserverCurrent.SplittingRoots.exactAllRoots

theorem fixed_nonzeroRoots : Targets.NonzeroRoots :=
  LogicLineages.CartierObserverCurrent.SplittingRoots.nonzeroRoots

theorem fixed_frobeniusFixedPolynomial : Targets.FrobeniusFixedPolynomial :=
  LogicLineages.CartierObserverCurrent.SplittingRoots.frobeniusFixedPolynomial

theorem fixed_frobeniusRootPermutation : Targets.FrobeniusRootPermutation :=
  LogicLineages.CartierObserverCurrent.SplittingRoots.frobeniusRootPermutation

theorem fixed_fixedFieldExactlyF2 : Targets.FixedFieldExactlyF2 :=
  LogicLineages.CartierObserverCurrent.SplittingRoots.fixedFieldExactlyF2

#audit_namespace LogicLineages.CartierObserverCurrent.SplittingRoots.StatementChecks
end LogicLineages.CartierObserverCurrent.SplittingRoots.StatementChecks
