module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastChecks
open NumberedWindowInternalSparseSelectedLeastTargets

theorem exact_SelectedPackedLeast : ExactSelectedPackedLeast := by
  obtain ⟨C, cover, _⟩ := NumberedWindowInternalSparseCoverScratchNumericChecks.exact_SelectedCoverToScratch
  refine ⟨C, cover, ?_⟩
  intro s
  obtain ⟨X, W, exchange, window, _⟩ :=
    NumberedWindowInternalSparseScalarEdgeNumericChecks.exact_SelectedPackedScalarEdge s
  exact ⟨X, W, exchange, window,
    NumberedWindowInternalSparsePackedLeastNumericChecks.exact_PackedLeastComposition
      s C X W cover exchange window⟩

#print axioms exact_SelectedPackedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSelectedLeastChecks
