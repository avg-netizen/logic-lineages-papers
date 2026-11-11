module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryProof
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
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open OriginalUniverseDecoderTransportBindingProof OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderTransportShapeProof OriginalTypedDecoderTransportContextProof
open OriginalUniverseDecoderTransportUnaryAcceptanceProof OriginalTypedDecoderTransportUnaryWitnessProof
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The child acceptance is derived from the ORIGINAL accepted parent and
then transported by internal strong induction at its strictly smaller raw
input. Only this lambda child's own cutoff increases. -/
theorem lambdaAt (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw out d cutoff gamma extended typ domain child childOut requestedDomain codomain childGamma childExtended c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (hchild : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) childOut d (suc cutoff) child)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hg : Nonempty (Derivation body Delta (StepCons childGamma domain gamma)))
    (he : Nonempty (Derivation body Delta (StepCons childExtended domain extended)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W false typ raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W false typ out (targetContext erasing gamma extended) c)) := by
  have old := iffForward
    (lambdaIff H M W raw domain child typ requestedDomain codomain
      (sourceContext erasing gamma extended) (sourceContext erasing childGamma childExtended) c
      hc ht (sourceCons erasing domain gamma extended childGamma childExtended hg he)) ha
  have typed := andRight (andRight old)
  have fields := lambdaFields raw cutoff domain child hc
  have smaller := unaryChildStrict raw child (andLeft fields) (andLeft (andRight fields))
  have transported := belowRawApply H M W erasing false raw child d (suc cutoff)
    childGamma childExtended codomain childOut c hind smaller
    (childInsert d cutoff gamma extended domain childGamma childExtended hi hg he) hchild
    (andRight (andRight typed))
  have newShape := lambdaShape erasing raw out d cutoff domain child childOut hc hchild ho
  exact iffBackward
    (lambdaIff H M W out domain childOut typ requestedDomain codomain
      (targetContext erasing gamma extended) (targetContext erasing childGamma childExtended) c
      newShape ht (targetCons erasing domain gamma extended childGamma childExtended hg he))
    (andIntro (andLeft old) (andIntro (andLeft (andRight old))
      (andIntro (andLeft typed) (andIntro (andLeft (andRight typed)) transported))))

theorem lambdaBranch (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw out d cutoff gamma extended typ domain child c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W false typ raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W false typ out (targetContext erasing gamma extended) c)) := by
  apply lambdaWitnesses erasing domain gamma extended d cutoff child typ
  intro beta j Theta childGamma childExtended childOut requestedDomain codomain hj hg he hchild ht
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [graph2Rename] at hc'
  rw [insertRename] at hi'
  rw [graph3Rename] at ho'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact lambdaAt H M W erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) (domain.relabel j) (child.relabel j)
    childOut requestedDomain codomain childGamma childExtended (c.relabel j) hind' hc' hi' ho' hchild ht hg he ha'

theorem ordinaryAt (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw out d cutoff gamma extended typ head base baseOut headData result types c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (hbase : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) baseOut d cutoff base)))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W false typ raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W false typ out (targetContext erasing gamma extended) c)) := by
  have old := iffForward
    (ordinaryIff H M W raw head base headData result types typ (sourceContext erasing gamma extended) c hc hh ht) ha
  have typed := andRight (andRight old)
  have fields := ordinaryFields raw cutoff head base hc
  have smaller := unaryChildStrict raw base (andLeft fields) (andLeft (andRight fields))
  have transported := belowRawApply H M W erasing true raw base d cutoff gamma extended types baseOut c
    hind smaller hi hbase (andRight (andRight typed))
  have newShape := ordinaryShape erasing raw out d cutoff head base baseOut hc hbase ho
  exact iffBackward
    (ordinaryIff H M W out head baseOut headData result types typ (targetContext erasing gamma extended) c newShape hh ht)
    (andIntro (andLeft old) (andIntro (andLeft (andRight old))
      (andIntro (andLeft typed) (andIntro (andLeft (andRight typed)) transported))))

theorem ordinaryBranch (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw out d cutoff gamma extended typ head base c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H M W false typ raw (sourceContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta
      (Accepted H M W false typ out (targetContext erasing gamma extended) c)) := by
  apply ordinaryWitnesses H erasing head base d cutoff
  intro beta j Theta headData result types baseOut hj hh ht hbase
  simp only [acceptedRename,targetContextRename]
  have hind' := renameInto hind j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hind'
  rw [graph2Rename] at hc'
  rw [insertRename] at hi'
  rw [graph3Rename] at ho'
  simp only [acceptedRename,sourceContextRename] at ha'
  exact ordinaryAt H M W erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) (head.relabel j) (base.relabel j)
    baseOut headData result types (c.relabel j) hind' hc' hi' ho' hbase hh ht ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryProof
