module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open OriginalInternalDecorationCoordinatesProof (pairRecover)
open OriginalInternalReturnRootProjectionSupportProof (popRecover consRecover)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualFramedReturnContent : FramedReturnTargets.ActualFramedReturnContent := by
 intro R body alpha Delta input work results frame suffix payload packed parameter first second output outWork stack value old root tail returned row
   hs hw hf hr hp hq hfirst hsecond hrun hout hstack hvalue htail
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hreturn := andRight (FramedReturnStateProof.actualFramedReturnState R body alpha Delta
   input work results frame suffix payload output hs hw hf hr hrun)
 have hpop := popRecover R input work results frame suffix payload output hs hw hf hr hreturn
 have hpair := pairRecover OriginalHereditaryReturnStep.rest
   (consOf (OriginalHereditaryReturnStep.termValue R) OriginalHereditaryReturnStep.oldSuffix)
   output outWork stack xs hpop hout
 have hcons := consRecover (OriginalHereditaryReturnStep.termValue R) OriginalHereditaryReturnStep.oldSuffix
   stack value old xs (andRight hpair) hstack
 let rootP : Program 1 := .composition (OriginalRootObservation.rootObservation R)
   ![OriginalHereditaryReturnStep.packed,OriginalHereditaryReturnStep.parameter]
 let returnP : Program 1 := .composition OriginalHereditaryReturn.returnRoot
   ![OriginalHereditaryReturnStep.packed,OriginalHereditaryReturnStep.firstSlot,OriginalHereditaryReturnStep.secondSlot]
 have hv := pairRecover rootP (pairOf returnP OriginalHereditaryReturnStep.deletionRow)
   value root tail xs (andLeft hcons) hvalue
 have ht := pairRecover returnP OriginalHereditaryReturnStep.deletionRow tail returned row xs (andRight hv) htail
 have hroot := binaryRecover (OriginalRootObservation.rootObservation R)
   OriginalHereditaryReturnStep.packed OriginalHereditaryReturnStep.parameter root packed parameter xs
   (andLeft hv) hp hq
 have hreturned := ternaryRecover OriginalHereditaryReturn.returnRoot OriginalHereditaryReturnStep.packed
   OriginalHereditaryReturnStep.firstSlot OriginalHereditaryReturnStep.secondSlot returned packed first second xs
   (andLeft ht) hp hfirst hsecond
 exact andIntro hroot (andIntro hreturned (andIntro (andRight ht) (andRight hcons)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnContentProof
