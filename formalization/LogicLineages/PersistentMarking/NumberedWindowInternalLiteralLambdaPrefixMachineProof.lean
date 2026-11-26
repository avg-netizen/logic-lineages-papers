module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixMachineProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (conjunction branch constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelope (applyUnary cursor field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseRawTick (stateFrame rowBody emitState)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaHeadTest lambdaWitnessTest lambdaFrameGuard)
open NumberedWindowInternalLiteralLambdaLexicalGateProof

def rawTripleCall (p : Program 3) : Program 5 := .composition p ![.projection 2,.projection 3,.projection 4]

def isLambdaPrefix : Program 5 :=
  conjunction (rawTripleCall lambdaHeadTest) (rawTripleCall lambdaWitnessTest)

def prefixValidation (W : Program 3) : Program 5 :=
  conjunction (rawTripleCall lambdaFrameGuard) (lambdaLexicalGate W)

def prefixInnerWitness : Program 5 := lexicalSlot (field 0) 3

def prefixFrame (c t q w r : Program 5) : Program 5 :=
  .composition .succ (fun _ : Fin 1 =>
    consOf c (consOf t (consOf q (consOf w (consOf r (constantZero 5))))))

def prefixNext : Program 5 :=
  prefixFrame lexicalContext lexicalCodomain lexicalSourceBody prefixInnerWitness lexicalTargetBody

def prefixInitialFrame : Program 5 :=
  prefixFrame (.projection 0) (.projection 1) (.projection 2) (.projection 3) (.projection 4)

def prefixStart : Program 5 := emitState (constantOne 5) prefixInitialFrame

def prefixAccept : Program 5 := emitState (constantOne 5) (constantZero 5)
def prefixReject : Program 5 := emitState (constantZero 5) (constantZero 5)

/-- The real proof obligations at a lambda frame are the literal child
tape and live typed window on each raw body, at the same pushed binder.
Any non-lambda prefix stops successfully and leaves its raw checker
untouched. -/
def prefixLive (W : Program 3) : Program 5 :=
  branch isLambdaPrefix prefixAccept
    (branch (prefixValidation W) prefixReject (emitState (constantOne 5) prefixNext))

def prefixReadSlot : Nat → Program 1
  | 0 => applyUnary cellHead rowBody
  | n+1 => applyUnary (applyUnary cellHead (cursor n)) rowBody

def prefixPerform (W : Program 3) : Program 1 :=
  .composition (prefixLive W) ![prefixReadSlot 0,prefixReadSlot 1,prefixReadSlot 2,prefixReadSlot 3,prefixReadSlot 4]

def prefixTick (W : Program 3) : Program 1 :=
  branch stateFrame (.projection 0) (prefixPerform W)

def prefixLoop (W : Program 3) : Program 2 :=
  .recursion (.projection 0) (.composition (prefixTick W) (fun _ : Fin 1 => .projection 1))

def prefixOwnState (W : Program 3) : Program 5 :=
  .composition (prefixLoop W) ![.projection 3,prefixStart]

def prefixOwn (W : Program 3) : Program 5 :=
  .composition cellHead (fun _ : Fin 1 => prefixOwnState W)

def prefixFrameTerm {α : Type} (c t q w r : OTerm α) : OTerm α :=
  suc (packedBody [c,t,q,w,r])

def prefixStartTerm {α : Type} (c t q w r : OTerm α) : OTerm α :=
  stateTerm (suc z) (prefixFrameTerm c t q w r)

#print axioms prefixTick
#print axioms prefixOwn
#print axioms prefixStartTerm
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixMachineProof
