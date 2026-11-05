module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierPrograms

def encodeState (s : PlainFrontier.State) : Bool × List Nat :=
  (s.1, s.2.map NormalForm.Formula.encode)

namespace Code
abbrev State := Bool × List Nat

def advance (s : State) : State :=
  (s.1 || s.2.any (fun p => (PlainBranchSplitPrograms.Code.step p).1),
    s.2.flatMap (fun p => (PlainBranchSplitPrograms.Code.step p).2))
def run (n : Nat) (s : State) : State := advance^[n] s
def fuel (code : Nat) : Nat := (MaximalPlainBranchPrograms.Code.variables code).length + 1
def initial (code : Nat) : State := (false, [code])
def answer (code : Nat) : Bool := (run (fuel code) (initial code)).1
def decide (code : Nat) : Option Bool :=
  if MaximalPlainBranchPrograms.Code.isPlain code then some (answer code) else none
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierPrograms
