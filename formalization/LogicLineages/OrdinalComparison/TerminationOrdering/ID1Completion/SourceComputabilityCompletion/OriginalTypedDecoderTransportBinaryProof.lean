module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalContextInsertion
open OriginalContextInsertionSyntaxProof (insertRename)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportSyntaxProof
open OriginalTypedDecoderTransportBindingProof OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderTransportShapeProof OriginalTypedDecoderTransportContextProof
open OriginalTypedDecoderTransportBinaryAcceptanceProof OriginalTypedDecoderTransportBinaryWitnessProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationAt (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ domain fn arg arrow fnOut argOut : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ht : Nonempty (Derivation body Delta (StepCons arrow domain typ)))
    (hf : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) fnOut d cutoff fn)))
    (hg : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) argOut d cutoff arg)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  have old := iffForward (applicationIff H raw domain fn arg typ arrow (sourceContext erasing gamma extended) hc ht) ha
  have fields := applicationFields raw domain fn arg hc
  have smaller := binaryChildrenStrict raw fn arg (andLeft fields)
    (andLeft (andRight fields)) (andRight (andRight fields))
  have tf := belowRawApply H erasing false raw fn d cutoff gamma extended arrow fnOut
    hind (andLeft smaller) hi hf (andLeft old)
  have ta := belowRawApply H erasing false raw arg d cutoff gamma extended domain argOut
    hind (andRight smaller) hi hg (andRight old)
  have newShape := applicationShape erasing raw out d cutoff domain fn arg fnOut argOut hc hf hg ho
  exact iffBackward (applicationIff H out domain fnOut argOut typ arrow
    (targetContext erasing gamma extended) newShape ht) (andIntro tf ta)

theorem applicationBranch (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ domain fn arg : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  apply applicationWitnesses erasing domain typ fn arg d cutoff
  intro beta j Theta arrow fnOut argOut hj ht hf hg
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [graph3Rename] at hc' ho'
  rw [insertRename] at hi'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact applicationAt H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) (domain.relabel j)
    (fn.relabel j) (arg.relabel j) arrow fnOut argOut hind' hc' hi' ho' ht hf hg ha'

/-- Both numbered argument lists use their original distinct type lists.
The arbitrary label and recorded result remain untouched. -/
theorem numberedAt (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ label head recorded base extraTypes extras headData headResult baseTypes baseOut extrasOut : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData headResult baseTypes)))
    (hb : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) baseOut d cutoff base)))
    (he : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) extrasOut d cutoff extras)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  have old := iffForward (numberedIff H raw label head recorded base extraTypes extras headData headResult baseTypes
    typ (sourceContext erasing gamma extended) hc hh ht) ha
  have fields := numberedFields raw label head recorded base extraTypes extras hc
  have smaller := binaryChildrenStrict raw base extras (andLeft fields)
    (andLeft (andRight fields)) (andRight (andRight fields))
  have tb := belowRawApply H erasing true raw base d cutoff gamma extended baseTypes baseOut
    hind (andLeft smaller) hi hb (andLeft (andRight (andRight old)))
  have te := belowRawApply H erasing true raw extras d cutoff gamma extended extraTypes extrasOut
    hind (andRight smaller) hi he (andRight (andRight (andRight old)))
  have newShape := numberedShape erasing raw out d cutoff label head recorded base extraTypes extras baseOut extrasOut hc hb he ho
  exact iffBackward (numberedIff H out label head recorded baseOut extraTypes extrasOut headData headResult baseTypes
    typ (targetContext erasing gamma extended) newShape hh ht)
    (andIntro (andLeft old) (andIntro (andLeft (andRight old)) (andIntro tb te)))

theorem numberedBranch (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ label head recorded base extraTypes extras : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  apply numberedWitnesses H erasing head base extras d cutoff
  intro beta j Theta headData headResult baseTypes baseOut extrasOut hj hh ht hb he
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  simp only [programRename,tupleSixRename] at hc'
  rw [graph3Rename] at ho'
  rw [insertRename] at hi'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact numberedAt H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) (label.relabel j) (head.relabel j)
    (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j)
    headData headResult baseTypes baseOut extrasOut hind' hc' hi' ho' hh ht hb he ha'

theorem consAt (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended types domain head tail requestedDomain tailTypes headOut tailOut : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields types requestedDomain tailTypes)))
    (hh : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) headOut d cutoff head)))
    (hl : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) tailOut d cutoff tail)))
    (ha : Nonempty (Derivation body Delta (Accepted H true types raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H true types out (targetContext erasing gamma extended))) := by
  have old := iffForward (consIff H raw domain head tail types requestedDomain tailTypes
    (sourceContext erasing gamma extended) hc ht) ha
  have fields := consFields raw domain head tail hc
  have smaller := binaryChildrenStrict raw head tail (andLeft fields)
    (andLeft (andRight fields)) (andRight (andRight fields))
  have th := belowRawApply H erasing false raw head d cutoff gamma extended domain headOut
    hind (andLeft smaller) hi hh (andLeft (andRight (andRight old)))
  have tl := belowRawApply H erasing true raw tail d cutoff gamma extended tailTypes tailOut
    hind (andRight smaller) hi hl (andRight (andRight (andRight old)))
  have newShape := consShape erasing raw out d cutoff domain head tail headOut tailOut hc hh hl ho
  exact iffBackward (consIff H out domain headOut tailOut types requestedDomain tailTypes
    (targetContext erasing gamma extended) newShape ht)
    (andIntro (andLeft old) (andIntro (andLeft (andRight old)) (andIntro th tl)))

theorem consBranch (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended types domain head tail : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H true types raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (Accepted H true types out (targetContext erasing gamma extended))) := by
  apply consWitnesses erasing types head tail d cutoff
  intro beta j Theta requestedDomain tailTypes headOut tailOut hj ht hh hl
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [graph3Rename] at hc' ho'
  rw [insertRename] at hi'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact consAt H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (types.relabel j) (domain.relabel j)
    (head.relabel j) (tail.relabel j) requestedDomain tailTypes headOut tailOut
    hind' hc' hi' ho' ht hh hl ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryProof
