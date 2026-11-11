module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalRunStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalRunStateProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionBindingProof OriginalLambdaTraversalInternalIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeProof (fuelAtPayload)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem actualFuel (value parameter payload : OTerm alpha)
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value))) :
    Nonempty (Derivation positive Delta (graph2 fuel (payloadFuel payload) value parameter)) :=
  unaryValue InternalApplicationResultStack.fuel (.projection 0) (payloadFuel payload) value
    (Fin.cons value (Fin.cons parameter Fin.elim0)) (fuelAtPayload value payload hp)
    (projectionValue 0 (Fin.cons value (Fin.cons parameter Fin.elim0)))

theorem runAtStates (leaf : Program 2) (value parameter payload count produced start finish : OTerm alpha)
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel payload))))
    (hc : Nonempty (Derivation positive Delta (Completes leaf value parameter count produced)))
    (hi : Nonempty (Derivation positive Delta (graph2 initial start value parameter)))
    (hf : Nonempty (Derivation positive Delta (graph1 finishedState finish produced))) :
    Nonempty (Derivation positive Delta (graph2 (run leaf) finish value parameter)) := by
  apply finishedCases finish produced _ hf
  intro beta j Theta singleton hj hs he
  rw [graph2Rename]
  have hp' := renameInto hp j Theta hj
  have hb' := renameInto hb j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have hf' := renameInto hf j Theta hj
  rw [graph1Rename] at hp' hf'
  rw [graph2Rename] at hi'
  rw [weakBoundRename,payloadFuelRename] at hb'
  rw [completesRename] at hc'
  have ht := completesApply leaf (value.relabel j) (parameter.relabel j) (count.relabel j)
    (produced.relabel j) z z (start.relabel j) (finish.relabel j) hc'
    (initialAsVisit (start.relabel j) (value.relabel j) (parameter.relabel j) hi')
    (finishedAsReturn (finish.relabel j) (produced.relabel j) hf')
  have hrun := iteratePadding leaf (count.relabel j) (payloadFuel (payload.relabel j))
    (start.relabel j) (finish.relabel j) singleton hb' he ht
  exact binaryValue (iterate leaf) fuel initial (finish.relabel j)
    (payloadFuel (payload.relabel j)) (start.relabel j)
    (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hrun
    (actualFuel (value.relabel j) (parameter.relabel j) (payload.relabel j) hp') hi'

def stateQueries : Fin 2 → Program 3 :=
  ![.composition initial ![.projection 0,.projection 1],
    .composition finishedState (fun _ : Fin 1 => .projection 2)]

theorem runShapeAtQueries (leaf : Program 2) (value parameter payload count produced state : OTerm alpha)
    (ys : Fin 2 → OTerm alpha)
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel payload))))
    (hc : Nonempty (Derivation positive Delta (Completes leaf value parameter count produced)))
    (hr : Nonempty (Derivation positive Delta (graph2 (run leaf) state value parameter)))
    (hq : ∀ i, Nonempty (Derivation positive Delta (programGraph (stateQueries i) (ys i)
      (Fin.cons value (Fin.cons parameter (Fin.cons produced Fin.elim0)))))) :
    Nonempty (Derivation positive Delta (graph1 finishedState state produced)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons value (Fin.cons parameter (Fin.cons produced Fin.elim0))
  have hi := binaryRecover initial (.projection 0) (.projection 1) (ys 0) value parameter xs
    (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := unaryRecover finishedState (.projection 2) (ys 1) produced xs (hq 1) (projectionValue 2 xs)
  have hrun := runAtStates leaf value parameter payload count produced (ys 0) (ys 1) hp hb hc hi hf
  exact outputTransport finishedState (ys 1) state (Fin.cons produced Fin.elim0)
    (valueUnique (run leaf) (ys 1) state (Fin.cons value (Fin.cons parameter Fin.elim0)) hrun hr) hf

theorem completionRun (leaf : Program 2) (value parameter payload count produced state : OTerm alpha)
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel payload))))
    (hc : Nonempty (Derivation positive Delta (Completes leaf value parameter count produced)))
    (hr : Nonempty (Derivation positive Delta (graph2 (run leaf) state value parameter))) :
    Nonempty (Derivation positive Delta (graph1 finishedState state produced)) := by
  apply queryCases stateQueries (Fin.cons value (Fin.cons parameter (Fin.cons produced Fin.elim0))) _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hq
  have hp' := renameInto hp j Theta hj
  have hb' := renameInto hb j Theta hj
  have hc' := renameInto hc j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hp'
  rw [graph2Rename] at hr'
  rw [weakBoundRename,payloadFuelRename] at hb'
  rw [completesRename] at hc'
  exact runShapeAtQueries leaf (value.relabel j) (parameter.relabel j) (payload.relabel j)
    (count.relabel j) (produced.relabel j) (state.relabel j) ys hp' hb' hc' hr' hq

theorem completionFold (leaf : Program 2) (value parameter payload count produced : OTerm alpha)
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel payload))))
    (hc : Nonempty (Derivation positive Delta (Completes leaf value parameter count produced))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) produced value parameter)) := by
  apply programCases (run leaf) (Fin.cons value (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta state hj hr
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp j Theta hj
  have hb' := renameInto hb j Theta hj
  have hc' := renameInto hc j Theta hj
  rw [graph1Rename] at hp'
  rw [weakBoundRename,payloadFuelRename] at hb'
  rw [completesRename] at hc'
  exact unaryValue output (run leaf) (produced.relabel j) state
    (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (finishedOutput state (produced.relabel j)
      (completionRun leaf (value.relabel j) (parameter.relabel j) (payload.relabel j)
        (count.relabel j) (produced.relabel j) state hp' hb' hc' hr)) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionRunProof
