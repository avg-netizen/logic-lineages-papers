module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticLeastSchemasDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticLeastSchemasTargets
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility
open PositiveArithmeticSchemas PositiveArithmeticLeastSchemas OrdinaryArithmeticCarrier OrdinaryArithmeticDirect

def ActualSourceLeastSchemas : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty),
  ∃ scalar multiset : Positive (Fin 2), ∀ context : Nat,
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) ∧
    Calibrates multiset context (encodedList n arity Gamma context) (encodedDirect n arity Gamma context) ∧
    realize (fun x => x ∈ leastSet scalar context) (closureSchema (parameterizedBody scalar)) ![context] ∧
    realize (fun x => x ∈ leastSet multiset context) (closureSchema (parameterizedBody multiset)) ![context] ∧
    (∀ theta : language.Formula (Fin 1 ⊕ Fin 1),
      realize (fun x => x ∈ leastSet scalar context) (leastnessSchema (parameterizedBody scalar) theta) ![context]) ∧
    (∀ theta : language.Formula (Fin 1 ⊕ Fin 1),
      realize (fun x => x ∈ leastSet multiset context) (leastnessSchema (parameterizedBody multiset) theta) ![context])

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticLeastSchemasTargets
