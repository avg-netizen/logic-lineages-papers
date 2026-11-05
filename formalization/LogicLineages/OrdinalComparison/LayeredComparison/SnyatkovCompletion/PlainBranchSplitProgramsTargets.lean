module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsTargets
open NormalForm (Formula)
open PlainBranchSplitPrograms

def LiteralSmallCase : Prop := ∀ p : Formula,
  Code.small p.encode = (PlainBranchSplit.small p).encode ∧
  Code.smallAnswer p.encode = PlainBranchSplit.smallAnswer p

def LiteralBranchList : Prop := ∀ p : Formula,
  Code.branches p.encode = (PlainBranchSplit.branches p).map Formula.encode

def LiteralStep : Prop := ∀ p : Formula,
  Code.step p.encode = ((PlainBranchSplit.step p).1, (PlainBranchSplit.step p).2.map Formula.encode)

def ActualNumericPrograms : Prop :=
  Primrec Code.small ∧ Primrec Code.smallAnswer ∧ Primrec Code.branches ∧ Primrec Code.step

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsTargets
