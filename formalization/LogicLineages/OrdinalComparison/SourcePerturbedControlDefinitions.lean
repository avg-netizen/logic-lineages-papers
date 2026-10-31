module
public import LogicLineages.OrdinalComparison.ControlDefinitions
public import Mathlib.Computability.Primrec
public import Mathlib.Data.Real.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.PerturbedControl

/-- Bounded maximum search for the exponent of two. Every test is literal
integer divisibility; no valuation or bounded-simulation oracle is assumed. -/
def search (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => if n % (2^(k+1))=0 then k+1 else search n k
def valuationTwo (n : Nat) : Nat := if n=0 then 0 else search n n

/-- H is one fixed primitive-recursive Boolean bounded-simulation predicate,
as stipulated in the manuscript. The control-property theorem is stronger:
it works for ANY fixed primitive-recursive Boolean H, since no halting
completeness property is used in that lemma. This does not prove hardness. -/
def error (b : Nat) (H : Nat×Nat → Bool) (n : Nat) : Nat :=
  if n=0 then 0 else if n≤b then 0 else if H (valuationTwo n,n) then 1 else 0
def control (b : Nat) (H : Nat×Nat → Bool) (n : Nat) : Nat := Phi n+error b H n

/-- Literal real epsilon-N formulation of the displayed ratio limit. -/
def RatioLimit (b : Nat) (H : Nat×Nat → Bool) : Prop :=
  ∀ ε : Real, 0<ε → ∃ N : Nat, ∀ n : Nat, N≤n →
    |(control b H n : Real)/(Phi n : Real)-1|<ε
end LogicLineages.OrdinalComparison.PerturbedControl
