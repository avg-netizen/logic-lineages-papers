module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeTableDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMachineDefinitions
@[expose] public section
/-! Explicit ordinary finite-table codes for the bounded-prefix evaders.
This is a uniform code family, not a proof that the complete table numbering
is acceptable or that it matches existing Partrec-code runtime classes. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeCode
open Turing PredictionTapeTable

def entry (k index : Nat) : Option (Nat × Action) :=
  let q := index / 3
  if q ≤ k then
    if q = 0 then some (k + 1, .inr (some false))
    else if index % 3 = 0 then some (k + 2, .inr (some true))
    else some (q - 1, .inl true)
  else none

def table (k : Nat) : Table := (k, (List.range ((k + 3) * 3)).map (entry k))

def code (k : Nat) : Nat := Encodable.encode (table k)

def embedState (k : Nat) : PredictionTapeMachine.State k → Nat
  | .scan i => i.val
  | .done b => if b then k + 2 else k + 1

def embedCfg (k : Nat) (c : PredictionTapeMachine.Cfg k) : TM0.Cfg Symbol Nat :=
  ⟨embedState k c.q, c.Tape⟩

end LogicLineages.ComputabilityKnowledge.PredictionTapeCode
