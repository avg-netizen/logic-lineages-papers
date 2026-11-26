module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalBinaryProof
open OriginalTypedDecoderInternalApplicationSyntaxProof OriginalTypedDecoderInternalPushProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationForward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 applicationStep out state))) :
    Nonempty (Derivation body Delta (StepApplication out g t p suffix)) := by
  let qs : Fin 4 → Program 1 := ![domain,firstChild,secondChild,consOf domain typ]
  apply queryCases qs (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [stepApplicationRename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr' ho'
  simp only [consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hb := binaryFields payload (p.relabel j) (ys 0) (ys 1) (ys 2) xx hp'
    (hq 0) (hq 1) (hq 2)
  have ha := binaryRecover InternalListCodec.consCode domain typ
    (ys 3) (ys 0) (t.relabel j) xx (hq 3) (hq 0) ht'
  have hpush := pushTwoForward (constant 1 0) gamma (consOf domain typ) firstChild
    (constant 1 0) gamma domain secondChild rest
    (out.relabel j) (numeral 0) (g.relabel j) (ys 3) (ys 1)
    (numeral 0) (g.relabel j) (ys 0) (ys 2) (suffix.relabel j) xx
    (constantValue 0 xx) hg' (hq 3) (hq 1)
    (constantValue 0 xx) hg' (hq 0) (hq 2) hr' ho'
  exact stepApplicationIntro _ _ _ _ _ ys (andIntro hb (andIntro ha hpush))

theorem applicationBackward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepApplication out g t p suffix))) :
    Nonempty (Derivation body Delta (graph1 applicationStep out state)) := by
  apply stepApplicationCases out g t p suffix _ ho
  intro beta j Theta ys hj hq
  rw [graph1Rename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hd := binaryDomainValue payload (p.relabel j) (ys 0) (ys 1) (ys 2) xx hp' (andLeft hq)
  have hf := binaryFirstValue payload (p.relabel j) (ys 0) (ys 1) (ys 2) xx hp' (andLeft hq)
  have hs := binarySecondValue payload (p.relabel j) (ys 0) (ys 1) (ys 2) xx hp' (andLeft hq)
  have ha := binaryValue InternalListCodec.consCode domain typ
    (ys 3) (ys 0) (t.relabel j) xx (andLeft (andRight hq)) hd ht'
  exact pushTwoBackward (constant 1 0) gamma (consOf domain typ) firstChild
    (constant 1 0) gamma domain secondChild rest
    (out.relabel j) (numeral 0) (g.relabel j) (ys 3) (ys 1)
    (numeral 0) (g.relabel j) (ys 0) (ys 2) (suffix.relabel j) xx
    (constantValue 0 xx) hg' ha hf
    (constantValue 0 xx) hg' hd hs hr' (andRight (andRight hq))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationProof
