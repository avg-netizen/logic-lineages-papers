module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderInternalAcceptance OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atNil (H : Program 1) (M W : Program 2) (types raw gamma c payload : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H M W types raw gamma c)))
 (hp : Nonempty (Derivation body Delta (StepPair raw (numeral 6) payload))) :
 Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)) := by
 have hf := OriginalTypedDecoderTransportLogicalProof.iffForward
   (OriginalUniverseDecoderInternalAcceptanceLeafProof.nilIff H M W raw payload types gamma c hp) ha
 have he := andLeft hf
 rw [InternalControlGraphSupportProof.equalEqn] at he
 have hp0 := InternalApplicationValidityStackAppendRunProof.rightTransport InternalPairing.pairing
   raw (numeral 6) payload (numeral 0) he hp
 exact binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 0 6)
   (OriginalRawSyntaxTransport.constant 0 0) raw (numeral 6) (numeral 0) Fin.elim0 hp0
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 6 Fin.elim0)
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 Fin.elim0)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesNilProof
