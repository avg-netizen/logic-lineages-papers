module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.CrossIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Convert every original Encodable head occurrence before the raw cross product.
Invalid head encodings deliberately become raw0; no element is dropped. -/
def convertedHeads (n : Nat) : Program 1 := InternalListMap.map (OriginalEncodedHeadConversion.convert n)
/-- Same literal raw six-field branch, with ONLY slot1 converted. All five other
inputs are unchanged; map/cross preserve order and repeated occurrences. -/
def branch (n : Nat) : Program 6 := .composition OriginalNumberedEnumerationBranch.branch
  ![.projection 0,.composition (convertedHeads n) ![.projection 1],
    .projection 2,.projection 3,.projection 4,.projection 5]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch
