module
public import LogicLineages.PermittedControl.OriginalPrintedRawTerminalRowsTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawTerminalRows
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (TestCode)
open PreparedProjection (LowerOperandCode)

private theorem coordinatePrimitive : Primrec (fun n : Nat => ((0,n,(0,0,0,0)) : LowerOperandCode)) :=
  (Primrec.const 0).pair (Primrec.id.pair (Primrec.const (0,0,0,0)))

private theorem weightedPrimitive : Primrec weightedCode := by
  let A := Int × NormalForm.Code.ItemData
  have name : Primrec (fun t : A => t.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.fst.pair (coordinatePrimitive.comp name)

private theorem testPrimitive : Primrec₂ testCode := by
  have choose : Primrec (fun p : Nat × Nat => testCode p.1 p.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const ((1,0) : TestCode))
      ((Primrec.const 3).pair (Primrec.succ.comp Primrec.snd))
  exact choose.to₂

private theorem atomPrimitive : Primrec atomCode := by
  let A := NormalForm.Code.AtomData
  have kind : Primrec (fun p : A => p.1) := Primrec.fst
  have modulus : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have rawRow : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have signedConst : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp rawRow
  have source : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp rawRow
  have terms := Primrec.list_map source (weightedPrimitive.comp Primrec.snd).to₂
  exact (testPrimitive.comp kind modulus).pair (signedConst.pair terms)

private theorem tapePrimitive : Primrec rowsCode :=
  Primrec.list_map LinearRowsCodeProof.atoms_primitive
    ((atomPrimitive.comp LinearRowsCodeProof.decodeAtom_primitive).comp Primrec.snd).to₂

theorem exactOriginalRawTerminalRowsEffectivity : ExactOriginalRawTerminalRowsEffectivity :=
  ⟨weightedPrimitive,atomPrimitive,tapePrimitive⟩

end LogicLineages.PermittedControl.OriginalPrintedRawTerminalRows
