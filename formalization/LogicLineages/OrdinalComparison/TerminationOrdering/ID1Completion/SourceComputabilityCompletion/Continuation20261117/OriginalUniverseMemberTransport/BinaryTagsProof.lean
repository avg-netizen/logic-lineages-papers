module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BinaryTagsProof
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
open BinaryProof

theorem applicationTag (H : Program 1) (M N W : Program 2)
    (raw typ gamma c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases raw _ ht
  intro beta j Theta domain fn arg hj hc
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [acceptedRename] at ha'
  exact applicationBranch H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) domain fn arg (c.relabel j) hind' hc hinc' ha'

theorem numberedTag (H : Program 1) (M N W : Program 2)
    (raw typ gamma c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases raw _ ht
  intro beta j Theta label head recorded base types extras hj hc
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [acceptedRename] at ha'
  exact numberedBranch H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) label head recorded base types extras (c.relabel j) hind' hc hinc' ha'

theorem consTag (H : Program 1) (M N W : Program 2)
    (raw typ gamma c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W true typ raw gamma c)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ ht
  intro beta j Theta domain head tail hj hc
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [acceptedRename] at ha'
  exact consBranch H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) domain head tail (c.relabel j) hind' hc hinc' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BinaryTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BinaryTagsProof
