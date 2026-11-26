module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions RankArgumentInductionDefinitions
/-- Auxiliary raw-code induction, conditional only on the explicit local child weighting law.
The admitted spine, actual observation and raw rank, and AllSmall remain inside AtRaw. -/
def ActualAtRaw : Prop := ∀ (k : Nat) (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (parameter gamma c bound raw : OTerm alpha)
 (params : Fin k → OTerm alpha),
 Nonempty (Derivation body Delta (LocalWeights Q F H M W parameter gamma c bound params)) →
 Nonempty (Derivation body Delta (AtRaw Q F H M W parameter gamma c bound raw params))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionTargets
