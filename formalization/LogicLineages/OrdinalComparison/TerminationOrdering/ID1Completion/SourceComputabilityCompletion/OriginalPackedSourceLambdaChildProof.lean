module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open OriginalLambdaConstructor OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaConstructorGraphSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalTypedDecoderInternalListProof (consArrowFields)
open OriginalTypedDecoderTransportLogicalProof (iffForward)

theorem rawCoordinates (out b d e arrowCode : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (Fields out d e b arrowCode)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (node inner payload : OTerm beta), (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (out.relabel j) (arrowCode.relabel j) node)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing node (numeral 1) inner)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing inner (d.relabel j) payload)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (b.relabel j) (e.relabel j) payload)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let node : Program 1 := rightOf (.projection 0)
  let inner : Program 1 := rightOf node
  let qs : Fin 3 → Program 1 := ![node,inner,bodyPayload]
  let xs : Fin 1 → OTerm alpha := Fin.cons out Fin.elim0
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  have hf' := renameInto hf j Theta hj
  rw [fieldsRename] at hf'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (out.relabel j) Fin.elim0
  have hnode := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx
    (hq 0) (projectionValue 0 xx)
  have hinner := unaryRecover InternalUnpair.right node (ys 1) (ys 0) xx (hq 1) (hq 0)
  have hpayload := unaryRecover InternalUnpair.right inner (ys 2) (ys 1) xx (hq 2) (hq 1)
  have htag := unaryRecover InternalUnpair.left node (numeral 1) (ys 0) xx
    (andLeft hf') (hq 0)
  have hdomain := unaryRecover InternalUnpair.left inner (d.relabel j) (ys 1) xx
    (andLeft (andRight (andRight (andRight hf')))) (hq 1)
  have ho := reconstructPair (out.relabel j) (arrowCode.relabel j) (ys 0)
    (andLeft (andRight hf')) hnode
  have hn := reconstructPair (ys 0) (numeral 1) (ys 1) htag hinner
  have hi := reconstructPair (ys 1) (d.relabel j) (ys 2) hdomain hpayload
  have hb := bodyCodeRecover (b.relabel j) (e.relabel j) (out.relabel j) (ys 2)
    (andRight (andRight (andRight (andRight hf')))) (hq 2)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj ho hn hi hb

theorem sourceChild (H G : Program 1) (M W : Program 2)
    (out parameter b d e arrowCode c gamma extended childParam : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (Fields out d e b arrowCode)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) out parameter)))
    (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (hext : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam c extended))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) b childParam)) := by
  apply rawCoordinates out b d e arrowCode _ hf
  intro beta j Theta node inner payload hj ho hn hi hb
  simp only [graph2Rename,oneRename]
  have hf' := renameInto hf j Theta hj
  rw [fieldsRename] at hf'
  have hs' := renameInto hs j Theta hj
  have hparam' := renameInto hparam j Theta hj
  have hext' := renameInto hext j Theta hj
  have hcp' := renameInto hcp j Theta hj
  simp only [graph2Rename,oneRename] at hs' hparam' hext' hcp'
  have harrow := consArrowFields (arrowCode.relabel j) (d.relabel j) (e.relabel j)
    (andLeft (andRight (andRight hf')))
  have law := OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof.sourceLambdaCoordinatesIff
    H G M W (out.relabel j) (parameter.relabel j) (arrowCode.relabel j) node inner
    (d.relabel j) payload (d.relabel j) (e.relabel j) (b.relabel j)
    (c.relabel j) (gamma.relabel j) (extended.relabel j) (childParam.relabel j)
    ho hn hi harrow hb hparam' hext' hcp'
  exact andRight (iffForward law hs')

theorem actualSourceLambdaChild : OriginalPackedSourceLambdaChildTargets.ActualSourceLambdaChild := by
  intro body alpha Delta H G M W s parameter child d e arrow c gamma extended childParam
  exact sourceChild H G M W s parameter child d e arrow c gamma extended childParam

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
