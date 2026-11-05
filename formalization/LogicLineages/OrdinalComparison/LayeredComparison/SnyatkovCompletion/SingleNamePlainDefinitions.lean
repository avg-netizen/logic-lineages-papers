module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlain
open NormalForm

/-- Literal one-name plain-Phi syntax, including all zero and cancelled occurrences. -/
def admissible (i : Nat) (p : Formula) : Bool :=
  MaximalPlainBranch.isPlain p && p.variables.all (fun j => j == i)

/-- The bounded and large/maximal alternatives cover every natural witness in
this fragment. The original formula is retained in both actual compilers. -/
def existsEliminate (i : Nat) (p : Formula) : Formula :=
  .disjunction (BoundedRows.bounded i (MaximalPlainBranch.cutoff p) p)
    (MaximalPlainBranch.eliminate i p)
def forallEliminate (i : Nat) (p : Formula) : Formula :=
  .negative (existsEliminate i (.negative p))

namespace Code
def admissible (i code : Nat) : Bool :=
  MaximalPlainBranchPrograms.Code.isPlain code &&
    (MaximalPlainBranchPrograms.Code.variables code).all (fun j => j == i)
def existsEliminate (i code : Nat) : Nat :=
  ShiftedInputPrograms.Code.disjunction
    (BoundedRows.Code.bounded i (MaximalPlainBranchPrograms.Code.cutoff code) code)
    (MaximalPlainBranchPrograms.Code.eliminate i code)
def forallEliminate (i code : Nat) : Nat :=
  ShiftedInputPrograms.Code.negative (existsEliminate i (ShiftedInputPrograms.Code.negative code))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlain
