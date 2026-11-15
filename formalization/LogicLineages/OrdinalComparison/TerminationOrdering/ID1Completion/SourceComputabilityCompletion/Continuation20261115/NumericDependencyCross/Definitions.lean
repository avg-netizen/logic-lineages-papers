module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Row step [rightHead,tailRow,left]: prepend the ORIGINAL numeric pair. -/
def rowEntry : Program 3 := .composition InternalPairing.pairing ![.projection 2,.projection 0]
def rowStep : Program 3 := .composition InternalListCodec.consCode ![rowEntry,.projection 1]
/-- Inputs [rightList,left]. Literal map, preserving duplicates and order. -/
def row : Program 2 := InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) rowStep
/-- Outer step [leftHead,tailCross,rightList]: append THIS row before remaining rows. -/
def currentRow : Program 3 := .composition row ![.projection 2,.projection 0]
def crossStep : Program 3 := .composition InternalApplicationValidityStackAppend.append ![currentRow,.projection 1]
def cross : Program 2 := InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) crossStep
/-- UNGUARDED helper on [sourceRaw,targetRaw], not the decoded/default[] supplier.
No claim equates this helper with ExchangeNumericSuppliers.depsValue off-domain. -/
def rawDependencies : Program 2 := .composition cross
  ![.composition Continuation20261114.ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 0),
    .composition Continuation20261114.ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 1)]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross
