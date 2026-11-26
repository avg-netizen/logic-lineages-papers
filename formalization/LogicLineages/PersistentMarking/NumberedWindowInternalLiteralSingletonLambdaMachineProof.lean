module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundMachineProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaMachineProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalEqualityTest (predecessor)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)

def lambdaNodeType : Program 3 := onRaw (field 0) 2
def lambdaNodeBody : Program 3 := onRaw (field 1) 2

/-- The binder depth below one lambda: the successor of the tape's depth. -/
def binderDepth : Program 3 := .composition .succ (fun _ : Fin 1 => .projection 1)

/-- The child computation: the fallback on the same inserted code, the
bumped depth, and the literal body field of the node. -/
def lambdaChild (U : Program 3) : Program 3 :=
  .composition U ![.projection 0,binderDepth,lambdaNodeBody]

/-- A successful child is successor-packed; the rebuilt node stores its code. -/
def lambdaChildCode (U : Program 3) : Program 3 :=
  .composition predecessor (fun _ : Fin 1 => lambdaChild U)

def lambdaRebuiltCode (U : Program 3) : Program 3 :=
  consOf (literal 3 2) (consOf lambdaNodeType (consOf (lambdaChildCode U) (constantZero 3)))

def lambdaRebuilt (U : Program 3) : Program 3 :=
  .composition .succ (fun _ : Fin 1 => lambdaRebuiltCode U)

/-- Zero remains failure: a failed child fails the node. -/
def lambdaInstance (U : Program 3) : Program 3 :=
  branch (lambdaChild U) (constantZero 3) (lambdaRebuilt U)

def singletonLambdaDispatch (U : Program 3) : Program 3 :=
  branch (onRaw rawLambdaShape 2) U (lambdaInstance U)

/-- The lambda row is physical and sits behind both syntax guards of
`singletonBound`. Its child call goes to the supplied fallback at the
bumped depth; this is one unfolding, not a self-referential program.
No numeric calibration of this definition is asserted here. -/
def singletonLambda (V : Program 1) (H : Program 2) (U : Program 3) : Program 3 :=
  singletonBound V H (singletonLambdaDispatch U)

#print axioms singletonLambda
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaMachineProof
