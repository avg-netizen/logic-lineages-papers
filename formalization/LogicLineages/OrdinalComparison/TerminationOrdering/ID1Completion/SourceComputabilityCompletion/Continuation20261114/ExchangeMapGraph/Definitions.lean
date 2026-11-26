module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Lookup step receives [encoded key/value pair, recursive lookup result,key]. -/
def entryKey : Program 3 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection 0)
def entryValue : Program 3 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 0)
def lookupStep : Program 3 := InternalAcceptance.branch
  (.composition InternalEqualityTest.equalityTest ![entryKey,.projection 2]) (.projection 1)
  (.composition .succ (fun _ : Fin 1 => entryValue))
/-- First-match Option lookup, input [association-list code,key]. None=0;
some value=successor value. This is NOT a total default-value lookup. -/
def lookup : Program 2 := InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) lookupStep
/-- mapGraph step receives [key, recursively mapped tail,association list]. -/
def found : Program 3 := .composition lookup ![.projection 2,.projection 0]
def mapStep : Program 3 := InternalAcceptance.branch found (.projection 1)
  (.composition InternalListCodec.consCode
    ![.composition InternalEqualityTest.predecessor (fun _ : Fin 1 => found),.projection 1])
/-- Literal nat_omega_rec mapGraph: missing keys are OMITTED, not zero-filled. -/
def mapGraph : Program 2 := InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) mapStep
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph
