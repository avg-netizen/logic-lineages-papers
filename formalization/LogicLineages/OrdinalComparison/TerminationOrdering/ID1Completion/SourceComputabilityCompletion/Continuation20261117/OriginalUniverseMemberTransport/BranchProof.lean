module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.KnownProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderTransportLogicalProof
open OriginalUniverseDecoderTransport (Accepted)
open OriginalUniverseDecoderTransportSyntaxProof (acceptedRename)
open OriginalTypedDecoderTransportContextProof
open OriginalTypedDecoderTransportBinaryAcceptanceProof (tupleSixRename)
open SourceComputabilityFormulaSupportProof (numeral)
open Definitions InductionDefinitions SyntaxProof BindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open KnownProof OriginalTypedDecoderTransportTagSupportProof

theorem step (H : Program 1) (M N W : Program 2) (arguments : Bool)
    (raw typ gamma c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W arguments typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W arguments typ raw gamma c)) := by
  apply rawTagCases raw
  · intro beta j Theta i payload hj ht hp
    simp only [acceptedRename]
    have hind' := renameInto hind j Theta hj
    have hinc' := renameInto hinc j Theta hj
    have ha' := renameInto ha j Theta hj
    rw [belowRawRename] at hind'
    rw [memberIncludedRename] at hinc'
    rw [acceptedRename] at ha'
    cases arguments
    · exact termKnown H M N W i (raw.relabel j) (typ.relabel j) (gamma.relabel j) payload (c.relabel j) hind' hinc' ha' ht hp
    · exact argumentsKnown H M N W i (raw.relabel j) (typ.relabel j) (gamma.relabel j) payload (c.relabel j) hind' hinc' ha' ht hp
  · intro beta j Theta tag payload hj hp hu
    simp only [acceptedRename]
    have ha' := renameInto ha j Theta hj
    rw [acceptedRename] at ha'
    exact OriginalUniverseDecoderTransportRejectedProof.unknown H M W arguments (raw.relabel j) tag payload
      (typ.relabel j) (gamma.relabel j) (c.relabel j) _ hp hu ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BranchProof
