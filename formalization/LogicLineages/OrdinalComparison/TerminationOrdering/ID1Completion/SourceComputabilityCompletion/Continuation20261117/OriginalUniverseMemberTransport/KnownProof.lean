module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.UnaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BinaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.KnownProof
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
open LeafProof UnaryTagsProof BinaryTagsProof
open OriginalUniverseDecoderTransportRejectedProof OriginalUniverseDecoderTransportTagSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (variableConstructorValue bottomConstructorValue)

theorem termKnown (H : Program 1) (M N W : Program 2) (i : Fin 8)
    (raw typ gamma payload c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral i.val) raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  revert ht hp
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))))) i
  · intro ht hp
    exact variableBranch H M N W raw payload typ gamma c (variableConstructorValue raw payload hp) hinc ha
  · intro ht hp
    exact lambdaTag H M N W raw typ gamma c hind ht hinc ha
  · intro ht hp
    exact applicationTag H M N W raw typ gamma c hind ht hinc ha
  · intro ht hp
    exact bottomBranch H M N W raw payload typ gamma c (bottomConstructorValue raw payload hp) hinc ha
  · intro ht hp
    exact ordinaryTag H M N W raw typ gamma c hind ht hinc ha
  · intro ht hp
    exact numberedTag H M N W raw typ gamma c hind ht hinc ha
  · intro ht hp
    exact termSix H M W raw payload typ gamma c _ hp ha
  · intro ht hp
    exact termSeven H M W raw payload typ gamma c _ hp ha

theorem argumentsKnown (H : Program 1) (M N W : Program 2) (i : Fin 8)
    (raw typ gamma payload c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true typ raw gamma c)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral i.val) raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (Accepted H N W true typ raw gamma c)) := by
  revert ht hp
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))))) i
  · intro ht hp
    exact argumentsOther H M W 0 (by decide) (by decide) raw payload typ gamma c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 1 (by decide) (by decide) raw payload typ gamma c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 2 (by decide) (by decide) raw payload typ gamma c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 3 (by decide) (by decide) raw payload typ gamma c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 4 (by decide) (by decide) raw payload typ gamma c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 5 (by decide) (by decide) raw payload typ gamma c _ hp ha
  · intro ht hp
    exact nilBranch H M N W raw typ gamma c (acceptedNilConstructor H M W raw payload typ gamma c hp ha) hinc ha
  · intro ht hp
    exact consTag H M N W raw typ gamma c hind ht hinc ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.KnownProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.KnownProof
