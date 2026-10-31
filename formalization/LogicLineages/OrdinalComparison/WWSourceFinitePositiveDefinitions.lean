module
public import LogicLineages.OrdinalComparison.WWSourceClassesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
/-- Refusing executable evaluator for closed positive finite syntax, with no
ordinal evaluation oracle and no collapse computation. -/
def finitePositiveValue : OrdinalExpression Γ → Option Nat
  | .one => some 1
  | .add f g => do return (← finitePositiveValue f) + (← finitePositiveValue g)
  | .emul f g => do return 2 ^ (← finitePositiveValue f) * (← finitePositiveValue g)
  | _ => none
end LogicLineages.OrdinalComparison.Source.SourceClasses
