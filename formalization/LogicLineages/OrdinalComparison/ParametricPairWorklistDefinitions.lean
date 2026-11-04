module
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairWorklist
open ParametricFinitePairCollapse
abbrev Task := Sum (Nat × Nat) Nat
abbrev State := List Task × List Nat
/-- Ordered rectangle, filtered by the exact two predecessor tests. -/
def children (G : Nat → Nat) (p : Nat × Nat) : List (Nat × Nat) :=
  ((List.range (p.1+1)).flatMap (fun a =>
    (List.range (G (pairNorm p)+1)).map (fun b => (a,b)))).filter
      (fun q => decide (Below q p ∧ pairNorm q≤G (pairNorm p)))
def combine (vs : List Nat) : Nat := vs.foldr (fun v n => max (v+1) n) 0
/-- Malformed underflow states are stuck; actual executions prove enough values. -/
def step (G : Nat → Nat) : State → State
  | ([],vs) => ([],vs)
  | (Sum.inl p::ts,vs) =>
      let qs := children G p
      (qs.map Sum.inl ++ Sum.inr qs.length::ts,vs)
  | (Sum.inr k::ts,vs) =>
      if k≤vs.length then (ts,combine (vs.take k)::vs.drop k)
      else (Sum.inr k::ts,vs)
def run (G : Nat → Nat) (fuel : Nat) (s : State) : State := (step G)^[fuel] s
def initial (p : Nat × Nat) : State := ([Sum.inl p],[])
def result : State → Option Nat
  | ([],[n]) => some n
  | _ => none
def evaluate (G : Nat → Nat) (p : Nat × Nat) (fuel : Nat) : Option Nat :=
  result (run G fuel (initial p))
def firstFuel (G : Nat → Nat) (p : Nat × Nat) : Part Nat :=
  Nat.rfind (fun n => Part.some (evaluate G p n).isSome)
end LogicLineages.OrdinalComparison.Source.ParametricPairWorklist
