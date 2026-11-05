module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecision
open NormalForm

/-- A finite ambient valuation; absent entries denote zero. -/
def valuation (values : List Nat) (i : Nat) : Nat := values.getD i 0

def fixedNames (xs : List Nat) (p : Formula) : List Nat :=
  p.variables.filter (fun i => !xs.contains i)
def pin (i n : Nat) : Formula := SourceTermGraph.equation (SourceTermGraph.numeralRow i n)
def frame (xs values : List Nat) (p : Formula) : Formula :=
  .conjunction p ((fixedNames xs p).foldr
    (fun i rest => .conjunction (pin i (valuation values i)) rest) .truth)

def forallPrefix (ν : Nat → Nat) : List Nat → Formula → Prop
  | [], p => p.eval ν
  | i :: xs, p => ∀ n : Nat, forallPrefix (Function.update ν i n) xs p

def decideExists (xs values : List Nat) (p : Formula) : Option Bool :=
  if MaximalPlainBranch.isPlain p then some (PlainFrontier.answer (frame xs values p)) else none

def decideForall (xs values : List Nat) (p : Formula) : Option Bool :=
  (decideExists xs values (.negative p)).map Bool.not

namespace Code
def fixedNames (xs : List Nat) (code : Nat) : List Nat :=
  (MaximalPlainBranchPrograms.Code.variables code).filter (fun i => !xs.contains i)
def pin (i n : Nat) : Nat := SourceTermGraph.Code.equation (SourceTermGraph.Code.numeralRow i n)
def frame (xs values : List Nat) (code : Nat) : Nat :=
  SourceTermGraph.Code.conjunction code ((fixedNames xs code).foldr
    (fun i rest => SourceTermGraph.Code.conjunction (pin i (values.getD i 0)) rest) 0)
def decideExists (xs values : List Nat) (code : Nat) : Option Bool :=
  if MaximalPlainBranchPrograms.Code.isPlain code then
    some (PlainFrontierPrograms.Code.answer (frame xs values code)) else none
def decideForall (xs values : List Nat) (code : Nat) : Option Bool :=
  (decideExists xs values (6 * code + 3)).map Bool.not
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecision
