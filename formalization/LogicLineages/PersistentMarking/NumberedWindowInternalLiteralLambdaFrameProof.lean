module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open ID1Completion.InternalAcceptance (conjunction branch constantZero)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalEqualityTest (equalityTest)
open NumberedWindowInternalSparseFieldCell (cellHead)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot sameSlot)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)

def lambdaWitnessTerm {α : Type} (inner : OTerm α) : OTerm α :=
  rawCons (numeral 1) (packedBody [inner])

def lambdaWitnessShape : Program 1 := nodeGood (literal 1 1) 1

def lambdaWitnessTest : Program 3 := onRaw lambdaWitnessShape 1

def lambdaFrameGuard : Program 3 :=
  conjunction (onRaw rawLambdaShape 0) (conjunction (onRaw rawLambdaShape 2) (sameSlot 0))

def emitLambdaFrame : Program 3 :=
  .composition .succ (fun _ : Fin 1 =>
    consOf (frameSlot 1 0) (consOf (frameSlot 0 1) (consOf (frameSlot 1 2) (constantZero 3))))

def chosenLambdaFrame : Program 3 := branch lambdaFrameGuard (constantZero 3) emitLambdaFrame

def lambdaHeadTest : Program 3 :=
  onRaw (.composition equalityTest ![cellHead,literal 1 2]) 0

def otherLambdaCases (other : Program 3) : Program 3 :=
  branch lambdaHeadTest other (constantZero 3)

/-- Only the original lambda witness is made physically openable. The
other context branches still use the supplied original fallback. -/
def lambdaFallback (other : Program 3) : Program 3 :=
  branch lambdaWitnessTest (otherLambdaCases other) chosenLambdaFrame

#print axioms lambdaWitnessTerm
#print axioms chosenLambdaFrame
#print axioms lambdaFallback
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameProof
