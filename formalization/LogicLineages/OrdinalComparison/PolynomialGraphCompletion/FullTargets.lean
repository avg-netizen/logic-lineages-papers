module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion

/-- Paper08 thm:graphs, including both the effective all-natural graph for
every nonzero polynomial limit and the literal total functional translation
of arbitrary fixed nesting and addition. -/
def FullPolynomialCollapseGraphs : Prop :=
  Targets.FullPolynomialHeadGraphs ∧ ExpressionTargets.FullExpressionGraphs

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion
