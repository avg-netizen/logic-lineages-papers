module
public import LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontendTargets
import LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocatorProof
import LogicLineages.PermittedControl.OriginalPrintedRawGraphRowsProof
import LogicLineages.PermittedControl.OriginalPrintedRawTerminalRowsProof
import LogicLineages.PermittedControl.OriginalPrintedRawClauseAssemblyProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontend
open OriginalPrintedRawGraphAllocator (exactOriginalRawGraphAllocator)
open OriginalPrintedRawGraphRows (exactOriginalRawGraphRows)
open OriginalPrintedRawTerminalRows (exactOriginalRawTerminalRows)
open OriginalPrintedRawClauseAssembly (exactOriginalRawClauseAssembly)

theorem exactOriginalRawFamilyFrontend : ExactOriginalRawFamilyFrontend := by
  intro known gs p positive
  unfold familyCode encodeInput
  simp only [exactOriginalRawGraphRows exactOriginalRawGraphAllocator known p gs,Option.map_some,
    finish,(exactOriginalRawTerminalRows p).1]
  exact congrArg some (exactOriginalRawClauseAssembly
    (OriginalNormalizedCircuitMatrix.rowsList (OriginalPrintedPlainMatrixInfiniteLow.circuit known gs p))
      (OriginalPlainTerminalMatrix.rows p) p positive)

end LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontend
