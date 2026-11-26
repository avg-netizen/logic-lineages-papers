module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedHeadConversion.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalNumberedEnumerationBranch.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedNumberedEnumerationBranch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Convert every original Encodable head occurrence before the raw cross product.
Invalid head encodings deliberately become raw0; no element is dropped. -/
def convertedHeads (n : Nat) : Program 1 := InternalListMap.map (LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedHeadConversion.convert n)
/-- Same literal raw six-field branch, with ONLY slot1 converted. All five other
inputs are unchanged; map/cross preserve order and repeated occurrences. -/
def branch (n : Nat) : Program 6 := .composition LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalNumberedEnumerationBranch.branch
  ![.projection 0,.composition (convertedHeads n) ![.projection 1],
    .projection 2,.projection 3,.projection 4,.projection 5]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedNumberedEnumerationBranch
