module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalPairingSumBounds InternalPairingSumBoundsArithmeticProof
open InternalUnpairReverseBoundsArithmeticProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem childLess (amount payload tail previous : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (weakBound amount payload)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc payload) tail)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess (add amount tail) previous)) := by
  obtain ⟨hb⟩ := addWeakRight amount payload tail hb
  obtain ⟨he⟩ := he
  exact ⟨orderRight (add amount tail)
    (trans (symm (leftSuccessor payload tail)) (symm he)) hb⟩

 theorem tailLess (payload tail previous : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc payload) tail)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess tail previous)) := by
  obtain ⟨hb⟩ := rightWeakAdd (body := body) (Gamma := Delta) payload tail
  obtain ⟨he⟩ := he
  exact ⟨orderRight tail (trans (symm (leftSuccessor payload tail)) (symm he)) hb⟩

 theorem applicationLess (fp ap payload tail previous : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (weakBound (childFuelSum fp ap) payload)))
    (he : Nonempty (Derivation body Delta (eqn previous (add (suc payload) tail)))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess (add (suc fp) (add (suc ap) tail)) previous)) := by
  obtain ⟨h⟩ := childLess (childFuelSum fp ap) payload tail previous hb he
  exact ⟨orderLeft previous (associativity (suc fp) (suc ap) tail) h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseArithmeticProof
