module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.UnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.UnaryTagsProof
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
open UnaryProof

theorem lambdaTag (H : Program 1) (M N W : Program 2)
    (raw typ gamma c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  apply OriginalRawSyntaxTransportInternalParserUnaryProof.lambdaCases raw _ ht
  intro beta j Theta domain child hj hc
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [acceptedRename] at ha'
  exact lambdaBranch H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) domain child (c.relabel j) hind' hc hinc' ha'

theorem ordinaryTag (H : Program 1) (M N W : Program 2)
    (raw typ gamma c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  apply OriginalRawSyntaxTransportInternalParserUnaryProof.ordinaryCases raw _ ht
  intro beta j Theta head base hj hc
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [acceptedRename] at ha'
  exact ordinaryBranch H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) head base (c.relabel j) hind' hc hinc' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.UnaryTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.UnaryTagsProof
