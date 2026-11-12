module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalIndexedObserverDefinitions OriginalIndexedObserverRangeSyntaxProof
open OriginalContextInsertionLengthProof
open OriginalLambdaTraversalInternalFieldsSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual traversal child parameter has a cons context, hence exactly
one additional cell. Only original selector graphs are used. -/
theorem lambdaAtCount (input d parameter childParameter cutoff count : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawDomain d input)))
    (hcp : Nonempty (Derivation body Delta
      (graph2 OriginalLambdaTraversal.childParameter childParameter input parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 contextLength count parameter)))
    (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count))) :
    Nonempty (Derivation body Delta (ActualRange (suc cutoff) childParameter)) := by
  let ctx : Program 2 := leftOf (.projection 0)
  let gamma : Program 2 := rightOf (.projection 0)
  let extended : Program 2 := consOf (.projection 1) gamma
  let nextParameter : Program 2 := pairOf ctx extended
  let qs : Fin 4 → Program 2 := ![ctx,gamma,extended,nextParameter]
  let xs : Fin 2 → OTerm alpha := Fin.cons parameter (Fin.cons d Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [rangeRename,sucRelabel]
  have hd' := renameInto hd j Theta hj
  have hcp' := renameInto hcp j Theta hj
  have hl' := renameInto hl j Theta hj
  have hb' := renameInto hb j Theta hj
  simp only [graph1Rename,graph2Rename] at hd' hcp' hl'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hb'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (parameter.relabel j) (Fin.cons (d.relabel j) Fin.elim0)
  have hc := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (parameter.relabel j) xx
    (hq 0) (projectionValue 0 xx)
  have hg := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (parameter.relabel j) xx
    (hq 1) (projectionValue 0 xx)
  have he := binaryRecover InternalListCodec.consCode (.projection 1) gamma
    (ys 2) (d.relabel j) (ys 1) xx (hq 2) (projectionValue 1 xx) (hq 1)
  have hp := binaryRecover InternalPairing.pairing ctx extended
    (ys 3) (ys 0) (ys 2) xx (hq 3) (hq 0) (hq 2)
  have hparent := reconstructPair (parameter.relabel j) (ys 0) (ys 1) hc hg
  have hactual := OriginalLambdaBodyObjectSupportProof.childParameterAtPairs
    (input.relabel j) (d.relabel j) (ys 0) (ys 1) (parameter.relabel j) (ys 2) (ys 3)
    hd' hparent he hp
  have eqparam := valueUnique OriginalLambdaTraversal.childParameter (ys 3) (childParameter.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hactual hcp'
  have hp' := outputTransport InternalPairing.pairing (ys 3) (childParameter.relabel j)
    (Fin.cons (ys 0) (Fin.cons (ys 2) Fin.elim0)) eqparam hp
  have oldLength := unaryRecover OriginalContextInsertion.length InternalUnpair.right
    (count.relabel j) (ys 1) (Fin.cons (parameter.relabel j) Fin.elim0) hl' hg
  have newLength := lengthCons (ys 2) (d.relabel j) (ys 1) (count.relabel j) he oldLength
  have hright := pairRight (childParameter.relabel j) (ys 0) (ys 2) hp'
  have newContextLength := unaryValue OriginalContextInsertion.length InternalUnpair.right
    (suc (count.relabel j)) (ys 2) (Fin.cons (childParameter.relabel j) Fin.elim0) newLength hright
  exact rangeIntro (suc (cutoff.relabel j)) (childParameter.relabel j) (suc (count.relabel j))
    (andIntro newContextLength
      (InternalRecursionGraphExtensionSupportProof.successorOrder (cutoff.relabel j) (count.relabel j) hb'))

/-- The shifted cutoff remains below the actual child-context length. -/
theorem lambdaRange (input d e child parameter childParameter cutoff : OTerm alpha)
    (hf : Nonempty (Derivation body Delta
      (OriginalLambdaTraversalInternal.LambdaFields input d e child parameter childParameter)))
    (hr : Nonempty (Derivation body Delta (ActualRange cutoff parameter))) :
    Nonempty (Derivation body Delta (ActualRange (suc cutoff) childParameter)) := by
  apply rangeCases cutoff parameter _ hr
  intro beta j Theta count hj hcount
  simp only [rangeRename,sucRelabel]
  have hf' := renameInto hf j Theta hj
  rw [lambdaFieldsRename] at hf'
  exact lambdaAtCount (input.relabel j) (d.relabel j) (parameter.relabel j)
    (childParameter.relabel j) (cutoff.relabel j) count
    (andLeft (andRight hf')) (andRight (andRight (andRight (andRight hf'))))
    (andLeft hcount) (andRight hcount)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeProof
