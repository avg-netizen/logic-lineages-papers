module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeaf
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalEqualityTest (equalityTest)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)

/-- The function from the actual raw auxiliary source. Check its
original decoded header, not a new semantic test for reduction. -/
def lambdaHeader : Program 1 :=
  conjunction cellGood (.composition equalityTest ![cellHead,literal 1 2])

def functionLambdaHeader : Program 3 := .composition lambdaHeader ![frameSlot 2 0]

/-- The actual raw bottom term from the original source's result field. -/
def expectedBottom : Program 3 :=
  consOf (literal 3 3) (consOf (frameSlot 1 0) (constantZero 3))

def targetBottom : Program 3 := .composition equalityTest ![.projection 2,expectedBottom]

def leafAtAuxiliary (leaf : Nat → Program 3) (tag : Nat) : Program 3 :=
  let p := leaf tag
  if tag < 6 then branch sourceIsAux p (constantZero 3)
  else if tag = 6 then branch sourceIsAux p (conjunction p functionLambdaHeader)
  else if tag = 7 then branch sourceIsAux p (conjunction p targetBottom)
  else p

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeaf
