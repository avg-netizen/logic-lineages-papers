module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalTagArithmeticSyntaxProof
open InternalRelationalCRT
/-- No functionality, external choice sequence, or supplied residue term is assumed. -/
def ActualRelationalCRT : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n : OTerm α) (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)),
  Nonempty (Derivation body [] (((InternalBoundedCRT.pairwiseBelow t n) ⊓ availableBelow R n).imp
    (solution t R n)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTTargets
