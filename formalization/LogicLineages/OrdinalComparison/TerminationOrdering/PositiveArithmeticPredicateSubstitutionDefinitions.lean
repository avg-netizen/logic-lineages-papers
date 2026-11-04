module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitution
open FirstOrder Language PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
/-- The left summand holds parameters; the final singleton is the predicate argument. -/
def liftPredicateFormula {α : Type} (theta : language.Formula (α ⊕ Fin 1)) :
    language.Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
  theta.relabel (Sum.map (Sum.inl : α → α ⊕ Fin 1) id)

def substitutePredicate : {α : Type} → Positive α → language.Formula (α ⊕ Fin 1) → language.Formula α
  | _, .arithmetic phi, _ => arithmeticEmbedding.onFormula phi
  | _, .predicate t, theta => theta.subst (Sum.elim Term.var (fun _ => arithmeticEmbedding.onTerm t))
  | _, .conj p q, theta => substitutePredicate p theta ⊓ substitutePredicate q theta
  | _, .guarded guard p, theta => (arithmeticEmbedding.onFormula guard).imp (substitutePredicate p theta)
  | _, .all p, theta => allOne (substitutePredicate p (liftPredicateFormula theta))
end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitution
