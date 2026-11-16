module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (suc)
/-- Literal twice-size arithmetic term, not a replacement size/depth program. -/
def twice {alpha : Type} (size : OTerm alpha) : OTerm alpha := OrdinaryArithmetic.addTerm size size
/-- d ≤ 2*size expressed by the original strict order d < suc(2*size). -/
def termBound {alpha : Type} (depth size : OTerm alpha) : Formula alpha :=
  InternalLessThan.strictLess depth (suc (twice size))
/-- Argument-list depth has the indispensable +1 allowance, including nil. -/
def argumentsBound {alpha : Type} (depth size : OTerm alpha) : Formula alpha :=
  InternalLessThan.strictLess depth (suc (suc (twice size)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound
