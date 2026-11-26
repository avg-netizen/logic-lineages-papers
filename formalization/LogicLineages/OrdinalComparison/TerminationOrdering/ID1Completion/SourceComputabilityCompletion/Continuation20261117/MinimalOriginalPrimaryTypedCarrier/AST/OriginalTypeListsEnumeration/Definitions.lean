module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalTypeListsEnumeration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- [encoded inner list, remaining outer list, type code]: prepend the type
inside the inner list, then preserve that inner list as an outer-list entry. -/
def rowEntry : Program 3 := .composition InternalListCodec.consCode ![.projection 2,.projection 0]
def rowStep : Program 3 := .composition InternalListCodec.consCode ![rowEntry,.projection 1]
/-- Inputs [outer list of encoded type lists,type code]. -/
def row : Program 2 := InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) rowStep
/-- Inputs [type head,remaining cross rows,previous outer list]. -/
def currentRow : Program 3 := .composition row ![.projection 2,.projection 0]
def crossStep : Program 3 := .composition InternalApplicationValidityStackAppend.append ![currentRow,.projection 1]
/-- Inputs [type-code list,previous outer list]. Row-major order and duplicates. -/
def cross : Program 2 := InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) crossStep
/-- Nat recursion step [count,previous outer list,type-code list]: always prepend
empty type list before all nonempty lists, exactly as original typeLists. -/
def step : Program 3 := .composition InternalListCodec.consCode
  ![OriginalRawSyntaxTransport.constant 3 0,.composition cross ![.projection 2,.projection 1]]
/-- Inputs [length bound,type-code list]. Zero bound yields [[]], encoded1. -/
def enumeration : Program 2 := .recursion (InternalLessThan.constantOne 1) step
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalTypeListsEnumeration
