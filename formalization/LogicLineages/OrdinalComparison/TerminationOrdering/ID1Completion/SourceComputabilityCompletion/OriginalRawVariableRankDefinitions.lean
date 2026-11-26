module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRank
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The sum of the actual raw ranks of two arbitrary raw codes. This finite
composition exposes ordinary addition, with no successful-child premise. -/
def rankSum : Program 2 := .composition InternalArithmeticPrograms.addition
  ![.composition variableRankRaw (fun _ : Fin 1 => .projection 0),
    .composition variableRankRaw (fun _ : Fin 1 => .projection 1)]

/-- Ordinary arithmetic nonincrease: the old rank is not strictly below the
new rank. No replacement ordering or semantic natural-number valuation. -/
def RankNonincrease {alpha : Type} (after before : OTerm alpha) : Formula alpha :=
  (InternalLessThan.strictLess before after).not

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRank
