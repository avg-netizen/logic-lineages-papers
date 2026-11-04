module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemasProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSetProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSchemas
open PositiveArithmeticOperators

def parameterizedBody (body : Positive (Fin 2)) : Positive (Fin 1 ⊕ Fin 1) :=
  PositiveArithmeticTransforms.relabel ![Sum.inl 0,Sum.inr 0] body
end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSchemas
