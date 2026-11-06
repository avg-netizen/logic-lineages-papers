module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCoding
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof InternalCoprimeMultiple
/-- One original R-witness at each bounded object index, encoded by the unchanged betaFormula. -/
def codedBelow {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (a b n : OTerm α) : Formula α :=
  bounded (existsOne (R ⊓ arithmeticEmbedding.onFormula
    (OrdinaryArithmetic.betaFormula ((a.relabel Sum.inl).relabel Sum.inl)
      ((b.relabel Sum.inl).relabel Sum.inl) (.var (.inl (.inr 0))) (.var (.inr 0))))) n
/-- A single b is chosen outside all index and residue binders. -/
def codeWith {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (a n : OTerm α) : Formula α :=
  existsOne (codedBelow (R.relabel (Sum.map (Sum.map Sum.inl id) id))
    (a.relabel Sum.inl) (.var (.inr 0)) (n.relabel Sum.inl))
/-- One shared pair a,b precedes every object index and dependent relation witness. -/
def coding {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  existsOne (codeWith (R.relabel (Sum.map (Sum.map Sum.inl id) id))
    (.var (.inr 0)) (n.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCoding
