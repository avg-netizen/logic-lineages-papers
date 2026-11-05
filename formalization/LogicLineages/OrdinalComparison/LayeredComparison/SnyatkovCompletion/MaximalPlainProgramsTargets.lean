module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsTargets
open NormalForm MaximalPlainPrograms

def LiteralActiveGuard : Prop := ∀ (i : Nat) (r : Row),
  Code.ownIndices i (rowData r) = MaximalPlainRows.ownIndices i r ∧
    Code.activeGuard i (rowData r) = (MaximalPlainRows.activeGuard i r).encode

def LiteralResidueData : Prop := ∀ (i m : Nat) (r : Row),
  Code.residueRow i m (rowData r) = rowData (MaximalPlainRows.residueRow i m r)

def LiteralCutoffCompiler : Prop := ∀ (i : Nat) (a : Atom),
  Code.cutoff a.data = MaximalPlainRows.cutoff a ∧
    Code.compileAtom i a.data = (MaximalPlainRows.compileAtom i a).encode

def ActualGuardPrograms : Prop := Primrec₂ Code.ownIndices ∧ Primrec₂ Code.activeGuard

def ActualResidueProgram : Prop :=
  Primrec (fun p : Nat × Nat × NormalForm.Code.RowData => Code.residueRow p.1 p.2.1 p.2.2)

def ActualCompilerPrograms : Prop := Primrec Code.cutoff ∧ Primrec₂ Code.compileAtom

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsTargets
