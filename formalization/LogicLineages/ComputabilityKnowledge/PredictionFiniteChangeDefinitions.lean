module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section
/-! Paper14 lines300–315: the literal finite-test/change enumeration used in
its hardness construction, independently of the unresolved tape-runtime bridge.
Stage zero emits nothing; later stage t emits the fresh number t exactly when
its candidate differs from stage t−1. R is an arbitrary recursive Boolean
matrix, not assumed primitive recursive. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteChange

abbrev Matrix := Nat × Nat × Nat × Nat → Bool

def passes (R : Matrix) (z k s t : Nat) : Bool :=
  (List.range (t + 1)).all (fun u => R (z, k, s, u))

def candidate (R : Matrix) (z k t : Nat) : Nat :=
  (List.range (t + 1)).findIdx (fun s => passes R z k s t)

def changeEvent (R : Matrix) (z k t : Nat) : Bool :=
  decide (0 < t) && decide (candidate R z k t ≠ candidate R z k (t - 1))

def changeSet (R : Matrix) (z k : Nat) : Set Nat := {t | changeEvent R z k t = true}

def stageOutput (R : Matrix) (z k t : Nat) : Option Nat :=
  if changeEvent R z k t then some t else none

end LogicLineages.ComputabilityKnowledge.PredictionFiniteChange
