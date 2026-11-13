module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultShapeSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultLocalShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open RootResultDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualReturnShape (R : Program 2)
 (packed parameter output input work results frame payload : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame (numeral 0))))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)))
 (hq : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.parameter parameter input)))
 (ht : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) output input))) :
 Nonempty (Derivation body Delta (Shape R packed parameter output)) := by
 have hpop := OriginalInternalReturnRootProjectionSupportProof.popRecover R input work results frame (numeral 0) payload output
   hs hw hf hr ht
 let rootP : Program 1 := .composition (OriginalRootObservation.rootObservation R)
   ![OriginalHereditaryReturnStep.packed,OriginalHereditaryReturnStep.parameter]
 let tailP : Program 1 := pairOf
   (.composition OriginalHereditaryReturn.returnRoot
     ![OriginalHereditaryReturnStep.packed,OriginalHereditaryReturnStep.firstSlot,OriginalHereditaryReturnStep.secondSlot])
   OriginalHereditaryReturnStep.deletionRow
 let stackP : Program 1 := consOf (OriginalHereditaryReturnStep.termValue R) OriginalHereditaryReturnStep.oldSuffix
 let popP : Program 1 := OriginalHereditaryReturnStep.pop (OriginalHereditaryReturnStep.termValue R)
 let qs : Fin 6 → Program 1 := Fin.cons rootP (Fin.cons tailP
   (Fin.cons (OriginalHereditaryReturnStep.termValue R) (Fin.cons OriginalHereditaryReturnStep.oldSuffix
     (Fin.cons stackP (Fin.cons popP Fin.elim0)))))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (Fin.cons input Fin.elim0) _
 intro beta j ys Theta hinc hg
 simp only [consTermRename,emptyRename] at hg
 have hs' := renameInto hs j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hq' := renameInto hq j Theta hinc
 have hpop' := renameInto hpop j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename] at hs' hw' hp' hq' hpop'
 let xs : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
 have hrest := OriginalHereditaryReturnStepInternalSupportProof.restGraph
   (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (numeral 0) hs' hw'
 have hvalue := binaryRecover InternalPairing.pairing rootP tailP (ys 2) (ys 0) (ys 1) xs (hg 2) (hg 0) (hg 1)
 have hstack := binaryRecover InternalListCodec.consCode (OriginalHereditaryReturnStep.termValue R)
   OriginalHereditaryReturnStep.oldSuffix (ys 4) (ys 2) (ys 3) xs (hg 4) (hg 2) (hg 3)
 have hout := binaryRecover InternalPairing.pairing OriginalHereditaryReturnStep.rest stackP
   (ys 5) (numeral 0) (ys 4) xs (hg 5) hrest (hg 4)
 have heq := valueUnique popP (ys 5) (output.relabel j) xs (hg 5) hpop'
 have hactual := outputTransport InternalPairing.pairing (ys 5) (output.relabel j)
   (Fin.cons (numeral 0) (Fin.cons (ys 4) Fin.elim0)) heq hout
 have hroot := binaryRecover (OriginalRootObservation.rootObservation R)
   OriginalHereditaryReturnStep.packed OriginalHereditaryReturnStep.parameter
   (ys 0) (packed.relabel j) (parameter.relabel j) xs (hg 0) hp' hq'
 rw [RootResultShapeSyntax.shapeRename]
 exact RootResultShapeSyntax.shapeIntro R (packed.relabel j) (parameter.relabel j) (output.relabel j)
   (ys 4) (ys 2) (ys 3) (ys 0) (ys 1) (andIntro hactual (andIntro hstack (andIntro hvalue hroot)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultLocalShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultLocalShapeProof
