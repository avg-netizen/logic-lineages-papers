module
public import LogicLineages.StandardControlCurrent.SparseTargets
public import LogicLineages.OrdinalComparison.PeakOrbitProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent

/-- Reuse only after current-source comparison against the independently
frozen expanded current-paper proposition. -/
theorem sparsePeaks : SparseTargets.SparsePeaks :=
  OrdinalComparison.actualSparsePeaks

end LogicLineages.StandardControlCurrent
