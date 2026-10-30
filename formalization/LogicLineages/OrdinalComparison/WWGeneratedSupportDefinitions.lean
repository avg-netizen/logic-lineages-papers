module
public import LogicLineages.OrdinalComparison.WWGeneratedGradeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source

/-- Literal occurring components, retaining multiplicities and avoiding any
semantic variable-elimination test. -/
def ordinalExpressionVariables {Γ : List Ty} : OrdinalExpression Γ → List (OrdinalComponent Γ)
  | .var c => [c]
  | .zero | .one | .omega => []
  | .add f g | .emul f g | .collapse f g =>
      ordinalExpressionVariables f ++ ordinalExpressionVariables g

end LogicLineages.OrdinalComparison.Source
