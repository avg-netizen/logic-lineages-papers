module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.LeafProof
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
open OriginalUniverseDecoderTransportLeafAcceptanceProof

theorem variableBranch (H : Program 1) (M N W : Program 2)
    (raw payload typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw payload)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  have old := iffForward (variableIff H M W raw payload typ gamma c hc) ha
  exact iffBackward (variableIff H N W raw payload typ gamma c hc) (andIntro (memberApply M N c typ hinc (andLeft old)) (andRight old))

theorem bottomBranch (H : Program 1) (M N W : Program 2)
    (raw payload typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw payload)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  have old := iffForward (bottomIff H M W raw payload typ gamma c hc) ha
  exact iffBackward (bottomIff H N W raw payload typ gamma c hc) (andIntro (memberApply M N c typ hinc (andLeft old)) (andRight old))

theorem nilBranch (H : Program 1) (M N W : Program 2)
    (raw typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W true typ raw gamma c)) := by
  have old := iffForward (nilIff H M W raw typ gamma c hc) ha
  exact iffBackward (nilIff H N W raw typ gamma c hc) old

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.LeafProof
