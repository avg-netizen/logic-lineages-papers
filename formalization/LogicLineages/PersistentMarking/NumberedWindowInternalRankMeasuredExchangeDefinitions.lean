module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchange
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)

def RankFit (rank : Program 1) : Prop :=
  ∀ n, evaluate rank (n ::ᵥ nil) = rawRank n

/-- Preserve the actual old directed code as D. The extra same-rank
test precedes the actual paired and cover-guarded layers. -/
def rankedExchange (C : Program 3) (s : Settings) (rank : Program 1) (D : Program 2) : Program 2 :=
  guardedExchange C s (pairedExchange (measuredExchange rank D))

end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchange
