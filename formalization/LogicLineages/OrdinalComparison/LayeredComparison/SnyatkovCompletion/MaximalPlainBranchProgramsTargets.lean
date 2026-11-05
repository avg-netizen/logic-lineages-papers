module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsTargets
open NormalForm (Formula)
open MaximalPlainBranchPrograms

def LiteralBranchData : Prop := ∀ p : Formula,
  Code.isPlain p.encode = MaximalPlainBranch.isPlain p ∧
  Code.variables p.encode = p.variables ∧ Code.cutoff p.encode = MaximalPlainBranch.cutoff p

def LiteralFrame : Prop :=
  (∀ i c : Nat, Code.lowerGuard i c = (MaximalPlainBranch.lowerGuard i c).encode) ∧
  (∀ i j : Nat, Code.maximumGuard i j = (MaximalPlainBranch.maximumGuard i j).encode) ∧
  ∀ (i : Nat) (p : Formula), Code.frame i p.encode = (MaximalPlainBranch.frame i p).encode

def LiteralBranchCompiler : Prop := ∀ (i : Nat) (p : Formula),
  Code.compile i p.encode = (MaximalPlainBranch.compile i p).encode ∧
  Code.framed i p.encode = (MaximalPlainBranch.framed i p).encode ∧
  Code.eliminate i p.encode = (MaximalPlainBranch.eliminate i p).encode

def ActualDataPrograms : Prop := Primrec Code.isPlain ∧ Primrec Code.variables ∧ Primrec Code.cutoff

def ActualFramePrograms : Prop :=
  Primrec₂ Code.lowerGuard ∧ Primrec₂ Code.maximumGuard ∧ Primrec₂ Code.frame

def ActualBranchPrograms : Prop :=
  Primrec₂ Code.compile ∧ Primrec₂ Code.framed ∧ Primrec₂ Code.eliminate

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsTargets
