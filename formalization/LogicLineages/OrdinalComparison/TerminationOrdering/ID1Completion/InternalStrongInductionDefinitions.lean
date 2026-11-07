module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInduction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof

/-- Retain the distinguished object variable while introducing one more free
parameter. This is ordinary capture-avoiding renaming of the original formula. -/
def lift {α : Type} (theta : Formula (α ⊕ Fin 1)) :
    Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
  theta.relabel (Sum.map Sum.inl id)

/-- The literal first-order assertion that theta holds below the given
object-language bound. The formula may use the inductive predicate freely. -/
def below {α : Type} (theta : Formula (α ⊕ Fin 1))
    (t : OrdinaryArithmetic.Term α) : Formula α :=
  allOne ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula
    (.var (.inr 0)) (t.relabel Sum.inl))).imp theta)

def step {α : Type} (theta : Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 1) :=
  (below (lift theta) (.var (.inr 0))).imp theta

/-- Course-of-values induction in the original expanded first-order language.
No external well-foundedness or semantic truth is a premise. -/
def schema {α : Type} (theta : Formula (α ⊕ Fin 1)) : Formula α :=
  (allOne (step theta)).imp (allOne theta)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInduction
