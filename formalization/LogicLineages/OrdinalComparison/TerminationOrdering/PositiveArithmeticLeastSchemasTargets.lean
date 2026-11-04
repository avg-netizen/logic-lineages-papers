module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSchemasDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSchemasTargets
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticSchemas PositiveArithmeticLeastSchemas

def ActualParameterizedBodyTruth : Prop := ∀ (body : Positive (Fin 2)) (P : Nat → Prop) (context x : Nat),
  realize P (parameterizedBody body).formula (Sum.elim ![context] (fun _ => x)) ↔
    realize P body.formula ![context,x]

def ActualLeastClosureSchema : Prop := ∀ (body : Positive (Fin 2)) (context : Nat),
  realize (fun x => x ∈ leastSet body context) (closureSchema (parameterizedBody body)) ![context]

def ActualLeastLeastnessSchema : Prop := ∀ (body : Positive (Fin 2)) (context : Nat)
    (theta : language.Formula (Fin 1 ⊕ Fin 1)),
  realize (fun x => x ∈ leastSet body context) (leastnessSchema (parameterizedBody body) theta) ![context]

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSchemasTargets
