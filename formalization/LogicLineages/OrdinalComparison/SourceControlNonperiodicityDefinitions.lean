module
public import LogicLineages.OrdinalComparison.SourcePerturbedControlDefinitions
public import Mathlib.Computability.PartrecCode

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceControlNonperiodicity
/-- Explicit effective enumeration of blank-input partial-recursive programs. -/
def program (e : Nat) : Nat.Partrec.Code := Denumerable.ofNat Nat.Partrec.Code e
/-- Monotone bounded evaln availability stage, not an asserted tape-step cost. -/
def boundedH (p : Nat × Nat) : Bool := (Nat.Partrec.Code.evaln p.2 (program p.1) 0).isSome
def gamma (b : Nat) : Nat → Nat := PerturbedControl.control b boundedH
/-- A computable point above both fixed cutoffs, with exact two-adic valuation e. -/
def fiberBase (N b e : Nat) : Nat := 2^e * (2*(max N b+1)+1)
def fiberPoint (N b p e k : Nat) : Nat := fiberBase N b e + k*p*2^(e+1)
def EventuallyPeriodicParity (b : Nat) : Prop :=
  ∃ N p : Nat, 0 < p ∧ ∀ n : Nat, N ≤ n → gamma b (n+p) % 2 = gamma b n % 2
end LogicLineages.OrdinalComparison.SourceControlNonperiodicity
