module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollection
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof InternalCoprimeMultiple
/-- The original relation conjoined with a strict, uniform object witness bound. -/
def boundedRelation {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (K : OTerm α) :
    Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
  R ⊓ arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula (.var (.inr 0))
    ((K.relabel Sum.inl).relabel Sum.inl))
/-- Every index has an original relation witness below the same K. -/
def boundBelow {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (K n : OTerm α) : Formula α :=
  InternalRelationalCRT.availableBelow (boundedRelation R K) n
/-- The object witness bound is chosen before the object bounded universal. -/
def collection {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  existsOne (boundBelow (R.relabel (Sum.map (Sum.map Sum.inl id) id))
    (.var (.inr 0)) (n.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollection
