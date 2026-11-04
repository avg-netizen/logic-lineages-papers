module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemas
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution SourceComputabilityFormulaSupportProof

def predicateAtObject {α : Type} : language.Formula (α ⊕ Fin 1) :=
  (Positive.predicate (.var (.inr (0 : Fin 1)))).formula

def closureSchema {α : Type} (body : Positive (α ⊕ Fin 1)) : language.Formula α :=
  allOne (body.formula.imp predicateAtObject)

def leastnessSchema {α : Type} (body : Positive (α ⊕ Fin 1))
    (theta : language.Formula (α ⊕ Fin 1)) : language.Formula α :=
  (allOne ((substitutePredicate body (liftPredicateFormula theta)).imp theta)).imp
    (allOne (predicateAtObject.imp theta))
end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemas
