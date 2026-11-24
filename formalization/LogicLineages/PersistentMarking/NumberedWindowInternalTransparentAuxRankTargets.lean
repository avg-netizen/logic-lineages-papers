module
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck earlierAt measureAt)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)

def RankCalibrated (g : Program 1) : Prop :=
  ∀ n, evaluate g (n ::ᵥ nil) = rawRank n

/-- The physical tag-six guard checks only the actual function slot's
earlier position. It never requests an argument rank. -/
def rankGuard : Program 4 := conjunction shapeCheck (earlierAt 2)

def rankAtFn : Program 4 :=
  branch (measureAt 2) (constantZero 4) (unaryAfter .succ (measureAt 2))

def rankUpdate (g : Program 1) : Program 4 :=
  branch rankGuard (unaryAfter g currentKey) rankAtFn

def auxRank (g : Program 1) : Program 1 := selectedMeasure (rankUpdate g)

end LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankTargets
