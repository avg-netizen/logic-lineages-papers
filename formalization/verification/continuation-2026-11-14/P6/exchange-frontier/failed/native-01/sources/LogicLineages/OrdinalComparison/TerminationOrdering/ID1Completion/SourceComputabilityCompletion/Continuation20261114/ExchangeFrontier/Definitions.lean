module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Right-fold step [node,flattened tail,parameter]; append literal dependencies
before the tail. Duplicates and Cartesian dependency order are preserved. -/
def flattenStep (D : Program 2) : Program 3 :=
  .composition InternalApplicationValidityStackAppend.append
    ![.composition D ![.projection 0,.projection 2],.projection 1]
def flatten (D : Program 2) : Program 2 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) (flattenStep D)
def singleton : Program 2 :=
  .composition InternalListCodec.consCode ![.projection 0,InternalAcceptance.constantZero 2]
/-- Iteration inputs [depth,seed,parameter], recursion step inputs
[predecessor depth,previous frontier,seed,parameter]. -/
def bindStep (D : Program 2) : Program 4 :=
  .composition (flatten D) ![.projection 1,.projection 3]
def bindList (D : Program 2) : Program 3 := .recursion singleton (bindStep D)
/-- Literal original code-pair frontier, not a dense rank row enumeration. -/
def originalFrontier {n : Nat} (source target : NumberedAuxiliaryCoding.Code (Fin n)) :
    Nat → List (NumberedAuxiliaryCoding.Code (Fin n) × NumberedAuxiliaryCoding.Code (Fin n))
  | 0 => [(source,target)]
  | k+1 => (originalFrontier source target k).flatMap NumberedExchangeCodeFieldsProof.dependencies
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier
