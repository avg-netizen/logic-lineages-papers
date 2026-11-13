module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackSource
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open ComputedStackDefinitions ComputedStackSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualComputedSingleton : ComputedStackTargets.ActualComputedSingleton := by
 intro R body H G M W alpha Delta packed parameter output hsource hcompleted
 let typP : Program 2 := leftOf (.projection 0)
 let rawP : Program 2 := rightOf (.projection 0)
 let cP : Program 2 := leftOf (.projection 1)
 let gammaP : Program 2 := rightOf (.projection 1)
 let rawJobP : Program 2 := pairOf rawP (.projection 1)
 let typedP : Program 2 := pairOf typP rawJobP
 let jobP : Program 2 := OriginalHereditaryEvaluatorDefinitions.job
 let branchP : Program 2 := .composition OriginalHereditaryFuelProgram.branching (fun _ : Fin 1 => jobP)
 let zeroP : Program 2 := OriginalRawSyntaxTransport.constant 2 0
 let visitP : Program 2 := pairOf zeroP jobP
 let workP : Program 2 := consOf visitP zeroP
 let qs : Fin 14 → Program 2 := Fin.cons typP (Fin.cons rawP (Fin.cons cP (Fin.cons gammaP
   (Fin.cons rawJobP (Fin.cons typedP (Fin.cons jobP (Fin.cons branchP (Fin.cons visitP (Fin.cons workP
     (Fin.cons OriginalHereditaryEvaluatorDefinitions.initial
       (Fin.cons OriginalHereditaryEvaluatorDefinitions.computedFuel
         (Fin.cons (OriginalHereditaryEvaluatorDefinitions.completed R)
           (Fin.cons (rightOf (OriginalHereditaryEvaluatorDefinitions.completed R)) Fin.elim0)))))))))))))
 let xs : Fin 2 → OTerm alpha := Fin.cons packed (Fin.cons parameter Fin.elim0)
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hinc hg
 let xx : Fin 2 → OTerm beta := Fin.cons (packed.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hg
 have hsource' := renameInto hsource j Theta hinc
 have hcompleted' := renameInto hcompleted j Theta hinc
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsource' hcompleted'
 have htyp := unaryRecover InternalUnpair.left (.projection 0) (ys 0) (packed.relabel j) xx (hg 0) (projectionValue 0 xx)
 have hraw := unaryRecover InternalUnpair.right (.projection 0) (ys 1) (packed.relabel j) xx (hg 1) (projectionValue 0 xx)
 have hc := unaryRecover InternalUnpair.left (.projection 1) (ys 2) (parameter.relabel j) xx (hg 2) (projectionValue 1 xx)
 have hgamma := unaryRecover InternalUnpair.right (.projection 1) (ys 3) (parameter.relabel j) xx (hg 3) (projectionValue 1 xx)
 have hp := reconstructPair (packed.relabel j) (ys 0) (ys 1) htyp hraw
 have hparameter := reconstructPair (parameter.relabel j) (ys 2) (ys 3) hc hgamma
 have hrawJob := binaryRecover InternalPairing.pairing rawP (.projection 1) (ys 4) (ys 1) (parameter.relabel j)
   xx (hg 4) (hg 1) (projectionValue 1 xx)
 have htyped := binaryRecover InternalPairing.pairing typP rawJobP (ys 5) (ys 0) (ys 4) xx (hg 5) (hg 0) (hg 4)
 have hz : Nonempty (Derivation body Theta (programGraph zeroP (numeral 0) xx)) :=
   OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx
 have hjob := binaryRecover InternalPairing.pairing zeroP typedP (ys 6) (numeral 0) (ys 5) xx (hg 6) hz (hg 5)
 have hbranch := unaryRecover OriginalHereditaryFuelProgram.branching jobP (ys 7) (ys 6) xx (hg 7) (hg 6)
 have hvisit := binaryRecover InternalPairing.pairing zeroP jobP (ys 8) (numeral 0) (ys 6) xx (hg 8) hz (hg 6)
 have hwork := binaryRecover InternalListCodec.consCode visitP zeroP (ys 9) (ys 8) (numeral 0) xx (hg 9) (hg 8) hz
 have hinitial := binaryRecover InternalPairing.pairing workP zeroP (ys 10) (ys 9) (numeral 0) xx (hg 10) (hg 9) hz
 have hfuel := unaryRecover OriginalHereditaryFuelProgram.fuel jobP (ys 11) (ys 6) xx (hg 11) (hg 6)
 have hrun := binaryRecover (OriginalHereditaryRuntimeIterationDefinitions.run R)
   OriginalHereditaryEvaluatorDefinitions.computedFuel OriginalHereditaryEvaluatorDefinitions.initial
   (output.relabel j) (ys 11) (ys 10) xx hcompleted' (hg 11) (hg 10)
 rw [shapeRename]
 exact ComputedStackSource.fromSource R body H G M W beta Theta (packed.relabel j) (parameter.relabel j)
   (ys 0) (ys 1) (ys 3) (ys 2) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 11) (ys 10) (output.relabel j)
   hp hparameter hrawJob htyped hjob hsource' hbranch hfuel hvisit hwork hinitial hrun hcompleted'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ComputedStackProof
