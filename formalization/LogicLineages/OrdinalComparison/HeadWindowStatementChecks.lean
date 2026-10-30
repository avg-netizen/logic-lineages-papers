module
public import LogicLineages.OrdinalComparison.HeadWindowProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualDifferentHeadStrictWindow : Targets.ActualDifferentHeadStrictWindow :=
  actualDifferentHeadStrictWindow
theorem fixed_actualFiniteHeadWindowLexicographic : Targets.ActualFiniteHeadWindowLexicographic :=
  actualFiniteHeadWindowLexicographic
theorem fixed_fullActualDifferentHeadWindow : Targets.FullActualDifferentHeadWindow :=
  fullActualDifferentHeadWindow

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
