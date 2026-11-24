module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositive

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddress
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparseAddressPositive (atAddress addressPositive)
open NumberedWindowInternalParameterizedAddressPositive (zeroAddress)

/-- The original physical target selector remains in slot two. -/
def targetRank (g : Program 1) : Program 3 := atAddress (applyUnary g rawLeast) 2

/-- Expose the actual rank-zero path without changing any positive answer.
All target ranks other than zero retain the old complete branch exactly. -/
def rankPartitionedAddress (cv tv g : Program 1) (raw : Program 5) (L : Program 3) : Program 3 :=
  branch (targetRank g) (zeroAddress cv tv g raw L) (addressPositive cv tv raw L)

end LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddress
