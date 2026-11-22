module
public import LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontendTargets
import LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocatorPrimitiveProof
import LogicLineages.PermittedControl.OriginalPrintedRawGraphRowsPrimitiveProof
import LogicLineages.PermittedControl.OriginalPrintedRawTerminalRowsPrimitiveProof
import LogicLineages.PermittedControl.OriginalPrintedRawClauseAssemblyPrimitiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontend
open HeterogeneousSignedMatrixSlice (RawRow)
open OriginalPrintedRawGraphAllocator (exactOriginalRawGraphAllocatorEffectivity)
open OriginalPrintedRawGraphRows (exactOriginalRawGraphRowsEffectivity)
open OriginalPrintedRawTerminalRows (exactOriginalRawTerminalRowsEffectivity)
open OriginalPrintedRawClauseAssembly (exactOriginalRawClauseEffectivity)

private theorem finishPrimitive : Primrec₂ finish := by
  let A := Args × List RawRow
  have input : Primrec (Prod.fst : A → Args) := Primrec.fst
  have orig : Primrec (fun p : A => p.1.1) := Primrec.fst.comp input
  have code : Primrec (fun p : A => p.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp orig)
  have pol : Primrec (fun p : A => p.1.2) := Primrec.snd.comp input
  have pre : Primrec (Prod.snd : A → List RawRow) := Primrec.snd
  have tail : Primrec (fun p : A => OriginalPrintedRawTerminalRows.rowsCode p.1.1.2.1) :=
    exactOriginalRawTerminalRowsEffectivity.2.2.comp code
  have h : Primrec (fun p : A => finish p.1 p.2) :=
    exactOriginalRawClauseEffectivity.2.2.comp (code.pair (pol.pair (pre.pair tail)))
  exact h.to₂

theorem originalRawFamilyFrontendEffectivity : OriginalRawFamilyFrontendEffectivity := by
  have graph : Primrec OriginalPrintedRawGraphRows.rowsCode :=
    exactOriginalRawGraphRowsEffectivity.2.2.2 exactOriginalRawGraphAllocatorEffectivity.2.2.2
  exact Primrec.option_map (graph.comp Primrec.fst) finishPrimitive

end LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontend
