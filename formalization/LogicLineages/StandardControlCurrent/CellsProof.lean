module
public import LogicLineages.StandardControlCurrent.CellsTargets
public import LogicLineages.OrdinalComparison.CollectedCellsProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.CellsProof

theorem full : CellsTargets.Full :=
  OrdinalComparison.fullActualCollectedCells

end LogicLineages.StandardControlCurrent.CellsProof
