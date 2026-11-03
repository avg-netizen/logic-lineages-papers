module
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseFormulaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BaseFormula.Targets
/-- Exact interpretation of actual literal BASE syntax under the SAME original
raw variables. Coded term values are not independent quantified parameters. -/
def LiteralBaseFormulaCode:Prop:=∀p:Formula,
  (∀ν:Nat→Nat,evaluate ν p.encode=true↔p.eval ν)∧rawVariables p.encode=p.variables
end LogicLineages.OrdinalComparison.LayeredComparison.BaseFormula.Targets
