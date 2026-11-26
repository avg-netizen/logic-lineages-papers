module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchFrame
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportRejectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof
open DispatchFrame
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {n : Nat} {H : Program 1} {arguments : Bool} {body : Positive (Fin 1)}
  {alpha : Type} {Delta : List (Formula alpha)}

theorem variableCode (f : Frame n H arguments body alpha Delta) (payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw (numeral 0) payload))) :
    Nonempty (Derivation body Delta f.conclusion) := by
  cases arguments
  · exact LeafProof.variableCode n f.raw payload f.pair f.size f.label f.depth
      (variableConstructorValue f.raw payload hp) f.guard f.bounds f.paired f.measured
  · exact OriginalTypedDecoderTransportRejectedProof.argumentsOther H 0 (by decide) (by decide)
      f.raw payload f.typ f.gamma f.conclusion hp f.typed

theorem bottom (f : Frame n H arguments body alpha Delta) (payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw (numeral 3) payload))) :
    Nonempty (Derivation body Delta f.conclusion) := by
  cases arguments
  · exact LeafProof.bottom n f.raw payload f.pair f.size f.label f.depth
      (bottomConstructorValue f.raw payload hp) f.guard f.bounds f.paired f.measured
  · exact OriginalTypedDecoderTransportRejectedProof.argumentsOther H 3 (by decide) (by decide)
      f.raw payload f.typ f.gamma f.conclusion hp f.typed

theorem nilCode (f : Frame n H arguments body alpha Delta) (payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw (numeral 6) payload)))
    (hz : Nonempty (Derivation body Delta (eqn payload z))) :
    Nonempty (Derivation body Delta f.conclusion) := by
  cases arguments
  · exact OriginalTypedDecoderTransportRejectedProof.termSix H f.raw payload f.typ f.gamma f.conclusion hp f.typed
  · exact LeafProof.nilCode n f.raw f.pair f.size f.label f.depth
      (OriginalEnumerationMembership.GuardPairProof.nil f.raw (numeral 6) payload hp ⟨refl _⟩ hz)
      f.guard f.bounds f.paired f.measured
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafDispatchProof
