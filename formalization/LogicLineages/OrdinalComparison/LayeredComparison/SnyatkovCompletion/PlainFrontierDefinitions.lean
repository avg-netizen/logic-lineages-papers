module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitDefinitions
public import Mathlib.Logic.Function.Iterate

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontier
open NormalForm
abbrev State := Bool × List Formula

def Meaning (s : State) : Prop :=
  s.1 = true ∨ ∃ p ∈ s.2, PlainLinearCleanup.Satisfiable p
def Plain (s : State) : Prop := ∀ p ∈ s.2, MaximalPlainBranch.isPlain p = true

/-- Keep every current literal branch; record successful finite cases and then
expand the entire finite frontier once. No semantic predicate is computed. -/
def advance (s : State) : State :=
  (s.1 || s.2.any (fun p => (PlainBranchSplit.step p).1),
    s.2.flatMap (fun p => (PlainBranchSplit.step p).2))
def run (n : Nat) (s : State) : State := advance^[n] s
/-- Original occurrence count is a simple effective upper bound on distinct
nonlinear names; the extra round exhausts even the zero-name case. -/
def fuel (p : Formula) : Nat := p.variables.length + 1
def initial (p : Formula) : State := (false, [p])
def answer (p : Formula) : Bool := (run (fuel p) (initial p)).1
def decide (p : Formula) : Option Bool :=
  if MaximalPlainBranch.isPlain p then some (answer p) else none

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontier
