module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.UnaryProof
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
open OriginalUniverseDecoderTransportUnaryAcceptanceProof OriginalTypedDecoderTransportUnaryWitnessProof

theorem lambdaAt (H : Program 1) (M N W : Program 2)
    (raw gamma typ domain child requestedDomain codomain childGamma c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hg : Nonempty (Derivation body Delta (StepCons childGamma domain gamma)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta
      (Accepted H N W false typ raw gamma c)) := by
  have old := iffForward
    (lambdaIff H M W raw domain child typ requestedDomain codomain
      gamma childGamma c
      hc ht hg) ha
  have typed := andRight (andRight old)
  have fields := lambdaFields raw (numeral 0) domain child hc
  have smaller := unaryChildStrict raw child (andLeft fields) (andLeft (andRight fields))
  have transported := belowRawApply H M N W false raw child codomain childGamma c hind smaller hinc (andRight (andRight typed))
  exact iffBackward
    (lambdaIff H N W raw domain child typ requestedDomain codomain
      gamma childGamma c
      hc ht hg)
    (andIntro (memberApply M N c typ hinc (andLeft old)) (andIntro (memberApply M N c domain hinc (andLeft (andRight old)))
      (andIntro (andLeft typed) (andIntro (andLeft (andRight typed)) transported))))

theorem lambdaBranch (H : Program 1) (M N W : Program 2)
    (raw gamma typ domain child c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  apply lambdaWitnesses false domain gamma gamma (numeral 0) (numeral 0) child typ
  intro beta j Theta childGamma childExtended childOut requestedDomain codomain hj hg he hchild ht
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [graph2Rename] at hc'
  rw [acceptedRename] at ha'
  exact lambdaAt H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) (domain.relabel j) (child.relabel j) requestedDomain codomain childGamma (c.relabel j) hind' hc' ht hg hinc' ha'

theorem ordinaryAt (H : Program 1) (M N W : Program 2)
    (raw gamma typ head base headData result types c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta
      (Accepted H N W false typ raw gamma c)) := by
  have old := iffForward
    (ordinaryIff H M W raw head base headData result types typ gamma c hc hh ht) ha
  have typed := andRight (andRight old)
  have fields := ordinaryFields raw (numeral 0) head base hc
  have smaller := unaryChildStrict raw base (andLeft fields) (andLeft (andRight fields))
  have transported := belowRawApply H M N W true raw base types gamma c hind smaller hinc (andRight (andRight typed))
  exact iffBackward
    (ordinaryIff H N W raw head base headData result types typ gamma c hc hh ht)
    (andIntro (memberApply M N c typ hinc (andLeft old)) (andIntro (andLeft (andRight old))
      (andIntro (andLeft typed) (andIntro (andLeft (andRight typed)) transported))))

theorem ordinaryBranch (H : Program 1) (M N W : Program 2)
    (raw gamma typ head base c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  apply ordinaryWitnesses H false head base (numeral 0) (numeral 0)
  intro beta j Theta headData result types baseOut hj hh ht hbase
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [graph2Rename] at hc'
  rw [acceptedRename] at ha'
  exact ordinaryAt H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) (head.relabel j) (base.relabel j) headData result types (c.relabel j) hind' hc' hh ht hinc' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.UnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.UnaryProof
