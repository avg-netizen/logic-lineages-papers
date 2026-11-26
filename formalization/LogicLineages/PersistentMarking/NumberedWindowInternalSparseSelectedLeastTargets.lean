module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)

/-- The same cover works for every setting. The exchange and packed-window
programs are selected for that setting and occur literally inside the least program. -/
def ExactSelectedPackedLeast : Prop :=
  ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ s : Settings, ∃ (X : Program 2) (W : Program 3),
      ActualTermExchange s X ∧ ActualPackedWindow s W ∧
      ActualLeastCalibration s (packedLeastProgram C X W s)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastTargets
