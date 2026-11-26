module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineRunStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineRunStateProof
open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletionBindingProof OriginalStructuralNodeSizeInternalMachineIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open OriginalLambdaTraversalInternalRunStateProof (finishedCases finishedAsReturn finishedOutput)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem runAtStates (d k raw count produced start finish : OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel raw))))
    (hc : Nonempty (Derivation positive Delta (Completes d k raw count produced)))
    (hi : Nonempty (Derivation positive Delta (graph3 initial start d k raw)))
    (hf : Nonempty (Derivation positive Delta (graph1 finishedState finish produced))) :
    Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSize.run) finish d k raw)) := by
  apply finishedCases finish produced _ hf
  intro beta j Theta singleton hj hs he
  rw [graph3Rename]
  have hb' := renameInto hb j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have hf' := renameInto hf j Theta hj
  rw [graph1Rename] at hf'
  rw [graph3Rename] at hi'
  rw [weakBoundRename,payloadFuelRename] at hb'
  rw [completesRename] at hc'
  have ht := completesApply (d.relabel j) (k.relabel j) (raw.relabel j) (count.relabel j)
    (produced.relabel j) z z (start.relabel j) (finish.relabel j) hc'
    (initialAsVisit (start.relabel j) (d.relabel j) (k.relabel j) (raw.relabel j) hi')
    (finishedAsReturn (finish.relabel j) (produced.relabel j) hf')
  have hrun := iteratePadding (count.relabel j) (payloadFuel (raw.relabel j))
    (start.relabel j) (finish.relabel j) singleton hb' he ht
  exact binaryValue (OriginalStructuralNodeSize.iterate) fuel initial (finish.relabel j)
    (payloadFuel (raw.relabel j)) (start.relabel j)
    ![d.relabel j,k.relabel j,raw.relabel j] hrun
    (actualFuel (d.relabel j) (k.relabel j) (raw.relabel j)) hi'

def stateQueries : Fin 2 → Program 4 :=
  ![.composition initial ![.projection 0,.projection 1,.projection 2],
    .composition finishedState (fun _ : Fin 1 => .projection 3)]

theorem foldAtQueries (d k raw count produced : OTerm alpha)
    (ys : Fin 2 → OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel raw))))
    (hc : Nonempty (Derivation positive Delta (Completes d k raw count produced)))
    (hq : ∀ i, Nonempty (Derivation positive Delta
      (programGraph (stateQueries i) (ys i) ![d,k,raw,produced]))) :
    Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalMachineCompletion.fold) produced d k raw)) := by
  let xs : Fin 4 → OTerm alpha := ![d,k,raw,produced]
  have hi := compositionRecover initial ![.projection 0,.projection 1,.projection 2]
    (ys 0) xs ![d,k,raw] (hq 0) (fun i =>
      Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
        (Fin.cases (projectionValue 2 xs) (fun a => Fin.elim0 a))) i)
  have hf := unaryRecover finishedState (.projection 3) (ys 1) produced xs
    (hq 1) (projectionValue 3 xs)
  exact unaryValue output (OriginalStructuralNodeSize.run) produced (ys 1) ![d,k,raw]
    (finishedOutput (ys 1) produced hf)
    (runAtStates d k raw count produced (ys 0) (ys 1) hb hc hi hf)

theorem completionFold (d k raw count produced : OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel raw))))
    (hc : Nonempty (Derivation positive Delta (Completes d k raw count produced))) :
    Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalMachineCompletion.fold) produced d k raw)) := by
  apply queryCases stateQueries (Fin.cons d (Fin.cons k (Fin.cons raw (Fin.cons produced Fin.elim0)))) _
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  rw [graph3Rename]
  have hb' := renameInto hb j Theta hj
  have hc' := renameInto hc j Theta hj
  rw [weakBoundRename,payloadFuelRename] at hb'
  rw [completesRename] at hc'
  exact foldAtQueries (d.relabel j) (k.relabel j) (raw.relabel j)
    (count.relabel j) (produced.relabel j) ys hb' hc' hq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRunProof
