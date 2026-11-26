module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderEncodedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderFuelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderFuelProof
open OriginalUniverseDecoder OriginalUniverseDecoderEncodedProof

theorem singletonFuel (H : Nat → Nat) (M W : Nat → Nat → Nat) (request context count : Nat)
    (h : OriginalTypedDecoder.requestRaw request + 1 ≤ count) :
    iterateValue H M W count (OriginalTypedDecoder.initialValue request) context = 0 ∨
      iterateValue H M W count (OriginalTypedDecoder.initialValue request) context = Nat.pair 1 0 := by
  rcases iterateRefines H M W count (OriginalTypedDecoder.initialValue request) context with hz | he
  · exact Or.inl hz
  · rw [he]
    exact OriginalTypedDecoderFuelProof.singletonFuel H request count h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderFuelProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderFuelProof
