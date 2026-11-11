module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableTypeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalTagArithmeticSyntaxProof InternalRecursionClosureLogicProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionVariableAtProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Acceptance of the actual original variable at the inserted index forces
its requested type to be the actual inserted type. This is the typing fact
needed to erase that variable to bottom d, not a type-window assumption. -/
 theorem acceptedType (typ d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (Insert d cutoff gamma extended)))
    (hv : Nonempty (Derivation body Gamma
      (OriginalVariableDecoder.graph (suc z) typ cutoff extended))) :
    Nonempty (Derivation body Gamma (eqn typ d)) := by
  obtain ⟨hs⟩ := variableAt (suc z) typ d cutoff gamma extended hi
  obtain ⟨hv⟩ := hv
  have ht : Nonempty (Derivation body Gamma (testSpec (suc z) typ d)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hs) hv⟩
  have he := closedApply
    (andRight (OriginalVariableDecoderEqualityProof.equalityEquation (body := body) (suc z) typ d)) ht
  exact InternalEqualityTestProof.equalityOfAcceptance typ d he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableTypeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableTypeProof
