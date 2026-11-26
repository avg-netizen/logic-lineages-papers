module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryProof
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
open OriginalTypedDecoderTransportUnaryAcceptanceProof OriginalTypedDecoderTransportUnaryWitnessProof
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The child acceptance is derived from the ORIGINAL accepted parent and
then transported by internal strong induction at its strictly smaller raw
input. Only this lambda child's own cutoff increases. -/
theorem lambdaAt (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ domain child childOut requestedDomain codomain childGamma childExtended : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (hchild : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) childOut d (suc cutoff) child)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
    (hg : Nonempty (Derivation body Delta (StepCons childGamma domain gamma)))
    (he : Nonempty (Derivation body Delta (StepCons childExtended domain extended)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta
      (Accepted H false typ out (targetContext erasing gamma extended))) := by
  have old := iffForward
    (lambdaIff H raw domain child typ requestedDomain codomain
      (sourceContext erasing gamma extended) (sourceContext erasing childGamma childExtended)
      hc ht (sourceCons erasing domain gamma extended childGamma childExtended hg he)) ha
  have fields := lambdaFields raw cutoff domain child hc
  have smaller := unaryChildStrict raw child (andLeft fields) (andLeft (andRight fields))
  have transported := belowRawApply H erasing false raw child d (suc cutoff)
    childGamma childExtended codomain childOut hind smaller
    (childInsert d cutoff gamma extended domain childGamma childExtended hi hg he) hchild
    (andRight (andRight old))
  have newShape := lambdaShape erasing raw out d cutoff domain child childOut hc hchild ho
  exact iffBackward
    (lambdaIff H out domain childOut typ requestedDomain codomain
      (targetContext erasing gamma extended) (targetContext erasing childGamma childExtended)
      newShape ht (targetCons erasing domain gamma extended childGamma childExtended hg he))
    (andIntro (andLeft old) (andIntro (andLeft (andRight old)) transported))

theorem lambdaBranch (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ domain child : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta
      (Accepted H false typ out (targetContext erasing gamma extended))) := by
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
  exact lambdaAt H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) (domain.relabel j) (child.relabel j)
    childOut requestedDomain codomain childGamma childExtended hind' hc' hi' ho' hchild ht hg he ha'

theorem ordinaryAt (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ head base baseOut headData result types : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (hbase : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) baseOut d cutoff base)))
    (hh : Nonempty (Derivation body Delta (graph1 H headData head)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta
      (Accepted H false typ out (targetContext erasing gamma extended))) := by
  have old := iffForward
    (ordinaryIff H raw head base headData result types typ (sourceContext erasing gamma extended) hc hh ht) ha
  have fields := ordinaryFields raw cutoff head base hc
  have smaller := unaryChildStrict raw base (andLeft fields) (andLeft (andRight fields))
  have transported := belowRawApply H erasing true raw base d cutoff gamma extended types baseOut
    hind smaller hi hbase (andRight (andRight old))
  have newShape := ordinaryShape erasing raw out d cutoff head base baseOut hc hbase ho
  exact iffBackward
    (ordinaryIff H out head baseOut headData result types typ (targetContext erasing gamma extended) newShape hh ht)
    (andIntro (andLeft old) (andIntro (andLeft (andRight old)) transported))

theorem ordinaryBranch (H : Program 1) (erasing : Bool)
    (raw out d cutoff gamma extended typ head base : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta
      (Accepted H false typ raw (sourceContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta
      (Accepted H false typ out (targetContext erasing gamma extended))) := by
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
  exact ordinaryAt H erasing (raw.relabel j) (out.relabel j) (d.relabel j) (cutoff.relabel j)
    (gamma.relabel j) (extended.relabel j) (typ.relabel j) (head.relabel j) (base.relabel j)
    baseOut headData result types hind' hc' hi' ho' hbase hh ht ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryProof
