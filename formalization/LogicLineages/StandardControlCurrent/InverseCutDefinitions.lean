module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseDefinitions
public import Mathlib.Computability.Primrec.Basic
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseCut
open OrdinalComparison LayeredComparison.SnyatkovInverse
abbrev Input := Nat × Nat × Nat × Nat × Nat × Nat
def lowerIndex (g inv : Nat → Nat) (lo : Nat) : Nat :=
  if lo ≤ g 0 then 0 else inv (lo-1)+1
def residueNext (a m r : Nat) : Nat := a + ((r+m-a%m)%m)
def candidate (g inv : Nat → Nat) (p : Input) : Nat :=
  residueNext (max p.1 (lowerIndex g inv p.2.2.1)) p.2.2.2.2.1 p.2.2.2.2.2
def answer (g inv : Nat → Nat) (p : Input) : Bool :=
  decide (0 < p.2.2.2.2.1 ∧ p.2.2.2.2.2 < p.2.2.2.2.1 ∧
    candidate g inv p ≤ p.2.1 ∧ g (candidate g inv p) ≤ p.2.2.2.1)
def Cut (g : Nat → Nat) (p : Input) : Prop :=
  ∃ x : Nat, p.1 ≤ x ∧ x ≤ p.2.1 ∧ p.2.2.1 ≤ g x ∧ g x ≤ p.2.2.2.1 ∧
    x % p.2.2.2.2.1 = p.2.2.2.2.2
end LogicLineages.StandardControlCurrent.InverseCut
