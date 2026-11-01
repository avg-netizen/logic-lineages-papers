module
public import LogicLineages.OrdinalComparison.SourcePeakWordDefinitions
public import LogicLineages.OrdinalComparison.SourceKernelMeasureDefinitions
public import LogicLineages.OrdinalComparison.SourceSignatureBudgetDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- The literal source pair: original h occurrences and EVERY auxiliary
principal occurrence. Kernel masses do not enter ONLY this measure. -/
def comparisonLiteralPairMeasure (E F : OneVariableComparisonExpr) : ComparisonSourceMeasureState :=
  ⟨comparisonLiteralSourceHeadCount E+comparisonLiteralSourceHeadCount F,
    (comparisonAuxiliarySourceWord E++comparisonAuxiliarySourceWord F).map Prod.fst⟩

def comparisonLiteralPairStep (budget : Nat) (next current : OneVariableComparisonExpr × OneVariableComparisonExpr) : Prop :=
  ComparisonSourceKernelStep budget (comparisonLiteralPairMeasure next.1 next.2)
    (comparisonLiteralPairMeasure current.1 current.2)

end LogicLineages.OrdinalComparison
