module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCompletedTerminationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCompletedTerminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualCompletedTermination : OriginalHereditaryCompletedTerminationTargets.ActualCompletedTermination := by
 intro R body H G M W alpha Delta packed parameter output hs ho
 let p : Program 2 := .projection 0
 let q : Program 2 := .projection 1
 let typ := leftOf p
 let raw := rightOf p
 let win := leftOf q
 let gamma := rightOf q
 let rawJob := pairOf raw q
 let typed := pairOf typ rawJob
 let zero := OriginalRawSyntaxTransport.constant 2 0
 let job := OriginalHereditaryEvaluatorDefinitions.job
 let branch : Program 2 := .composition OriginalHereditaryFuelProgram.branching (fun _ : Fin 1 => job)
 let visit := pairOf zero job
 let work := consOf visit zero
 let fuel := OriginalHereditaryEvaluatorDefinitions.computedFuel
 let initial := OriginalHereditaryEvaluatorDefinitions.initial
 let qs : Fin 12 → Program 2 := ![typ,raw,win,gamma,rawJob,typed,job,branch,visit,work,fuel,initial]
 let xs : Fin 2 → OTerm alpha := Fin.cons packed (Fin.cons parameter Fin.elim0)
 apply queryCases qs xs _
 intro beta j ys Theta hinc hq
 rw [OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
 let xx : Fin 2 → OTerm beta := Fin.cons (packed.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hx : (fun i => (xs i).relabel j) = xx := by
  funext i; exact Fin.cases rfl (fun k => Fin.cases rfl (fun t => Fin.elim0 t) k) i
 rw [hx] at hq
 have hs' := renameInto hs j Theta hinc
 have ho' := renameInto ho j Theta hinc
 simp only [graph2Rename,numeralRename] at hs' ho'
 have hz := constantValue (body:=body) (Delta:=Theta) 0 xx
 have hp := reconstructPair (packed.relabel j) (ys 0) (ys 1)
   (unaryRecover InternalUnpair.left p (ys 0) (packed.relabel j) xx (hq 0) (projectionValue 0 xx))
   (unaryRecover InternalUnpair.right p (ys 1) (packed.relabel j) xx (hq 1) (projectionValue 0 xx))
 have hc := reconstructPair (parameter.relabel j) (ys 2) (ys 3)
   (unaryRecover InternalUnpair.left q (ys 2) (parameter.relabel j) xx (hq 2) (projectionValue 1 xx))
   (unaryRecover InternalUnpair.right q (ys 3) (parameter.relabel j) xx (hq 3) (projectionValue 1 xx))
 have hr := binaryRecover InternalPairing.pairing raw q (ys 4) (ys 1) (parameter.relabel j) xx (hq 4) (hq 1) (projectionValue 1 xx)
 have ht := binaryRecover InternalPairing.pairing typ rawJob (ys 5) (ys 0) (ys 4) xx (hq 5) (hq 0) (hq 4)
 have hj := binaryRecover InternalPairing.pairing zero typed (ys 6) (numeral 0) (ys 5) xx (hq 6) hz (hq 5)
 have hb := unaryRecover OriginalHereditaryFuelProgram.branching job (ys 7) (ys 6) xx (hq 7) (hq 6)
 have hv := binaryRecover InternalPairing.pairing zero job (ys 8) (numeral 0) (ys 6) xx (hq 8) hz (hq 6)
 have hw := binaryRecover InternalListCodec.consCode visit zero (ys 9) (ys 8) (numeral 0) xx (hq 9) (hq 8) hz
 have hf := unaryRecover OriginalHereditaryFuelProgram.fuel job (ys 10) (ys 6) xx (hq 10) (hq 6)
 have hi := binaryRecover InternalPairing.pairing work zero (ys 11) (ys 9) (numeral 0) xx (hq 11) (hq 9) hz
 have hrun := binaryRecover (OriginalHereditaryRuntimeIterationDefinitions.run R) fuel initial (output.relabel j) (ys 10) (ys 11) xx ho' (hq 10) (hq 11)
 exact OriginalHereditarySourceRootCompletionProof.actualSourceRootCompletion R body H G M W beta Theta
   (packed.relabel j) (parameter.relabel j) (ys 0) (ys 1) (ys 3) (ys 2) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10) (ys 11) (output.relabel j)
   hp hc hr ht hj hs' hb hf hv hw hi hrun
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCompletedTerminationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCompletedTerminationProof
