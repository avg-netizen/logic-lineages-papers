module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BinaryProof
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
open OriginalUniverseDecoderTransportBinaryAcceptanceProof OriginalTypedDecoderTransportBinaryWitnessProof

theorem applicationAt (H : Program 1) (M N W : Program 2)
    (raw gamma typ domain fn arg arrow c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
    (ht : Nonempty (Derivation body Delta (StepCons arrow domain typ)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  have old := iffForward (applicationIff H M W raw domain fn arg typ arrow gamma c hc ht) ha
  have typed := andRight old
  have fields := applicationFields raw domain fn arg hc
  have smaller := binaryChildrenStrict raw fn arg (andLeft fields)
    (andLeft (andRight fields)) (andRight (andRight fields))
  have tf := belowRawApply H M N W false raw fn arrow gamma c hind (andLeft smaller) hinc (andLeft typed)
  have ta := belowRawApply H M N W false raw arg domain gamma c hind (andRight smaller) hinc (andRight typed)
  exact iffBackward (applicationIff H N W raw domain fn arg typ arrow
    gamma c hc ht) (andIntro (memberApply M N c typ hinc (andLeft old)) (andIntro tf ta))

theorem applicationBranch (H : Program 1) (M N W : Program 2)
    (raw gamma typ domain fn arg c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  apply applicationWitnesses false domain typ fn arg (numeral 0) (numeral 0)
  intro beta j Theta arrow fnOut argOut hj ht hf hg
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [graph3Rename] at hc'
  rw [acceptedRename] at ha'
  exact applicationAt H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) arrow (c.relabel j) hind' hc' ht hinc' ha'

theorem numberedAt (H : Program 1) (M N W : Program 2)
    (raw gamma typ label head recorded base extraTypes extras headData headResult baseTypes c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData headResult baseTypes)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  have old := iffForward (numberedIff H M W raw label head recorded base extraTypes extras headData headResult baseTypes
    typ gamma c hc hh ht) ha
  have typed := andRight (andRight old)
  have fields := numberedFields raw label head recorded base extraTypes extras hc
  have smaller := binaryChildrenStrict raw base extras (andLeft fields)
    (andLeft (andRight fields)) (andRight (andRight fields))
  have tb := belowRawApply H M N W true raw base baseTypes gamma c hind (andLeft smaller) hinc (andLeft (andRight (andRight typed)))
  have te := belowRawApply H M N W true raw extras extraTypes gamma c hind (andRight smaller) hinc (andRight (andRight (andRight typed)))
  exact iffBackward (numberedIff H N W raw label head recorded base extraTypes extras headData headResult baseTypes
    typ gamma c hc hh ht)
    (andIntro (memberApply M N c typ hinc (andLeft old)) (andIntro (andLeft (andRight old))
      (andIntro (andLeft typed) (andIntro (andLeft (andRight typed)) (andIntro tb te)))))

theorem numberedBranch (H : Program 1) (M N W : Program 2)
    (raw gamma typ label head recorded base extraTypes extras c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W false typ raw gamma c)) := by
  apply numberedWitnesses H false head base extras (numeral 0) (numeral 0)
  intro beta j Theta headData headResult baseTypes baseOut extrasOut hj hh ht hb he
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  simp only [programRename,tupleSixRename] at hc'
  rw [acceptedRename] at ha'
  exact numberedAt H M N W (raw.relabel j) (gamma.relabel j) (typ.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) headData headResult baseTypes (c.relabel j) hind' hc' hh ht hinc' ha'

theorem consAt (H : Program 1) (M N W : Program 2)
    (raw gamma types domain head tail requestedDomain tailTypes c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields types requestedDomain tailTypes)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W true types raw gamma c)) := by
  have old := iffForward (consIff H M W raw domain head tail types requestedDomain tailTypes
    gamma c hc ht) ha
  have fields := consFields raw domain head tail hc
  have smaller := binaryChildrenStrict raw head tail (andLeft fields)
    (andLeft (andRight fields)) (andRight (andRight fields))
  have th := belowRawApply H M N W false raw head domain gamma c hind (andLeft smaller) hinc (andLeft (andRight (andRight old)))
  have tl := belowRawApply H M N W true raw tail tailTypes gamma c hind (andRight smaller) hinc (andRight (andRight (andRight old)))
  exact iffBackward (consIff H N W raw domain head tail types requestedDomain tailTypes
    gamma c hc ht)
    (andIntro (andLeft old) (andIntro (andLeft (andRight old)) (andIntro th tl)))

theorem consBranch (H : Program 1) (M N W : Program 2)
    (raw gamma types domain head tail c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M N W raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (hinc : Nonempty (Derivation body Delta (MemberIncluded M N c)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma c))) :
    Nonempty (Derivation body Delta (Accepted H N W true types raw gamma c)) := by
  apply consWitnesses false types head tail (numeral 0) (numeral 0)
  intro beta j Theta requestedDomain tailTypes headOut tailOut hj ht hh hl
  simp only [acceptedRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hinc' := renameInto hinc j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [memberIncludedRename] at hinc'
  rw [graph3Rename] at hc'
  rw [acceptedRename] at ha'
  exact consAt H M N W (raw.relabel j) (gamma.relabel j) (types.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) requestedDomain tailTypes (c.relabel j) hind' hc' ht hinc' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BinaryProof
