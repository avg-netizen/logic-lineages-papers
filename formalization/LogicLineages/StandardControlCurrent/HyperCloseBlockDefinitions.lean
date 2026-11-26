module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HyperCloseBlock
open OrdinalComparison LayeredComparison.SnyatkovCompletion

def existsNames : List Nat → Matrix → (Nat → Nat) → Prop
  | [],p,ν => p.eval ν
  | x::xs,p,ν => ∃ n : Nat, existsNames xs p (Function.update ν x n)
def branches (xs : List Nat) (i j : Nat) (e h k l : Int) (c : Nat) (p : Matrix) : List (List Nat × Matrix) :=
  [(xs.erase i,HyperWindow.leftCases i j e h k l c p),
   (xs.erase j,HyperWindow.rightCases i j e h k l c p),
   (xs.erase i,HyperWindow.equalCases i j e h k l c p)]
def result (bs : List (List Nat × Matrix)) (ν : Nat → Nat) : Prop :=
  ∃ b ∈ bs, existsNames b.1 b.2 ν
abbrev Input := List Nat × HyperWindowCode.Input
def program (q : Input) : List (List Nat × Nat) :=
  [(q.1.erase (HyperWindowCode.leftName q.2),HyperWindowCode.leftCases q.2),
   (q.1.erase (HyperWindowCode.rightName q.2),HyperWindowCode.rightCases q.2),
   (q.1.erase (HyperWindowCode.leftName q.2),HyperWindowCode.equalCases q.2)]
end LogicLineages.StandardControlCurrent.HyperCloseBlock
