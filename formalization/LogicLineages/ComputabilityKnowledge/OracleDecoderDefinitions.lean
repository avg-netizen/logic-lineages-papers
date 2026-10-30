module

public import LogicLineages.ComputabilityKnowledge.OracleProgramDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleDecoder
open OracleProgram

def decodeFuel : Nat → Nat → Option Program
  | 0, _ => none
  | fuel + 1, index =>
      match index with
      | 0 => none
      | k + 1 =>
          let payload := k.unpair.2
          match k.unpair.1 with
          | 0 => some (.base (Denumerable.ofNat Nat.Partrec.Code payload))
          | 1 => if payload = 0 then some .query else none
          | 2 => do
              let p ← decodeFuel fuel payload.unpair.1
              let q ← decodeFuel fuel payload.unpair.2
              pure (.pair p q)
          | 3 => do
              let p ← decodeFuel fuel payload.unpair.1
              let q ← decodeFuel fuel payload.unpair.2
              pure (.comp p q)
          | 4 => do
              let p ← decodeFuel fuel payload.unpair.1
              let q ← decodeFuel fuel payload.unpair.2
              pure (.prec p q)
          | 5 => (decodeFuel fuel payload).map Program.mu
          | _ => none

def decode (index : Nat) : Option Program := decodeFuel (index + 1) index

def validIndex (index : Nat) : Bool := (decode index).isSome

def encodedDecode (index : Nat) : Option Nat := (decode index).map OracleProgram.encode

/-- Literal finite-table validation of the next index. No semantic validity
is carried as a field or assumed of the previous table. -/
def validationStep (previous : List Bool) : Bool :=
  match previous.length with
  | 0 => false
  | k + 1 =>
      let payload := k.unpair.2
      match k.unpair.1 with
      | 0 => true
      | 1 => decide (payload = 0)
      | 2 | 3 | 4 => previous.getD payload.unpair.1 false && previous.getD payload.unpair.2 false
      | 5 => previous.getD payload false
      | _ => false

end LogicLineages.ComputabilityKnowledge.OracleDecoder
