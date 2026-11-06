module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimality
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalCoprimeMultiple
open InternalTagArithmeticSyntaxProof
/-- The predecessor term of the literal beta modulus at the fresh index. -/
def betaFamily {α : Type} (b : OTerm α) : OTerm (α ⊕ Fin 1) :=
  OrdinaryArithmetic.mulTerm (OrdinaryArithmetic.succTerm (.var (.inr 0))) (b.relabel Sum.inl)
/-- Every positive difference at most n divides b, as an object bounded universal. -/
def differenceMultiples {α : Type} (b n : OTerm α) : Formula α :=
  dividesBelow (.var (.inr 0)) b n
/-- Existence of a positive common multiple, not an external finite product. -/
def positiveMultipleExists {α : Type} (n : OTerm α) : Formula α :=
  SourceComputabilityFormulaSupportProof.existsOne
    (differenceMultiples (OrdinaryArithmetic.succTerm (.var (.inr 0))) (n.relabel Sum.inl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimality
