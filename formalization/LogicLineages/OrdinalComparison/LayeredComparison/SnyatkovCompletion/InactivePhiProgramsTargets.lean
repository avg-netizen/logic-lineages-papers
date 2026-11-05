module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsTargets
open NormalForm InactivePhiPrograms

def LiteralPartitionData : Prop := ∀ (r : Row) (mask : List Bool),
  Code.remaining (rowData r) mask = rowData (InactivePhiRows.remaining r mask) ∧
    Code.dropped (rowData r) mask = rowData (InactivePhiRows.dropped r mask) ∧
    Code.onlyPhi (rowData r) = InactivePhiRows.onlyPhi r

def LiteralAdmissibleMasks : Prop := ∀ (i : Nat) (r : Row),
  (∀ mask : List Bool, Code.admissible i (rowData r) mask = InactivePhiRows.admissible i r mask) ∧
    Code.masks i (rowData r) = InactivePhiRows.masks i r

def LiteralGuardAndAtomCodes : Prop :=
  (∀ (r : Row) (mask : List Bool),
    Code.guard (rowData r) mask = (InactivePhiRows.guard r mask).encode) ∧
  (∀ (a : Atom) (r : Row), Code.withRow a.data (rowData r) = (InactivePhiRows.withRow a r).data)

def LiteralCompiler : Prop := ∀ (i : Nat) (a : Atom),
  Code.compileAtom i a.data = (InactivePhiRows.compileAtom i a).encode

def ActualMaskPrograms : Prop :=
  Primrec₂ Code.remaining ∧ Primrec₂ Code.dropped ∧ Primrec Code.onlyPhi ∧
    Primrec (fun p : Nat × NormalForm.Code.RowData × List Bool => Code.admissible p.1 p.2.1 p.2.2) ∧
    Primrec₂ Code.masks

def ActualCompilerPrograms : Prop := Primrec₂ Code.guard ∧ Primrec Code.any ∧ Primrec₂ Code.compileAtom

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsTargets
