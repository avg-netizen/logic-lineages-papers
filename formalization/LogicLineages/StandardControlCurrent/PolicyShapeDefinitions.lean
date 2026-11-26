module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyShape
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

def siteCode : MacroSite → Nat
  | .numeral => 0 | .positiveRepeat => 1 | .activeAdd => 2 | .activeExp => 3
  | .positiveAbstraction => 4 | .scalarRepeat => 5 | .optionalBoxTail => 6

def decodeSite : Nat → MacroSite
  | 0 => .numeral | 1 => .positiveRepeat | 2 => .activeAdd | 3 => .activeExp
  | 4 => .positiveAbstraction | 5 => .scalarRepeat | _ => .optionalBoxTail

def shapeCode {n : Nat} : Shape n → List Bool
  | .leaf => [false]
  | .join a b => shapeCode a ++ shapeCode b ++ [true]

abbrev State := Option (List Nat × List Nat)

def step : State → Bool → State
  | none, _ => none
  | some ([], _), false => none
  | some (x::xs, stack), false => some (xs, x::stack)
  | some (xs, r::l::stack), true => some (xs, node 4 l r::stack)
  | some (_, _), true => none

def run (script : List Bool) (state : State) : State := script.foldl step state

def finish : State → Option Nat
  | some ([], [x]) => some x
  | _ => none

def expandCode (script : List Bool) (xs : List Nat) : Option Nat :=
  finish (run script (some (xs, [])))

def selector (p : Policy) (tag n : Nat) : List Bool := shapeCode (p.shape (decodeSite tag) n)

def Effective (p : Policy) : Prop :=
  Computable (fun x : Nat × Nat => selector p x.1 x.2)

def macroCode (p : Policy) (tag n : Nat) (xs : List Nat) : Option Nat :=
  expandCode (selector p tag n) xs

def repeatCode (p : Policy) (tag count t : Nat) : Option Nat :=
  if count=0 then some 0 else macroCode p tag (count-1) (List.replicate count t)
end LogicLineages.StandardControlCurrent.PolicyShape
