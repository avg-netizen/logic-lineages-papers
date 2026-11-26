module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTagSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTagSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalLambdaConstructorGraphSyntaxProof (andLeft)
open OriginalRawSyntaxTransport
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderTransportTagSupportProof (nilConstructorFromPair)
open OriginalUniverseDecoderTransport
open OriginalUniverseDecoderInternalAcceptanceLeafProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The unchanged original nil guard forces a zero payload internally. -/
theorem acceptedNilConstructor (H : Program 1) (M W : Program 2) (raw payload types gamma c : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma c))) :
    Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)) := by
  have hi := closedApply (actualOriginalUniverseInternalNilAcceptance body H M W alpha raw payload types gamma c) hp
  exact nilConstructorFromPair raw payload hp (andLeft (iffForward hi ha))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTagSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTagSupportProof
