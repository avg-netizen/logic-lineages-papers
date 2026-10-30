module

public import LogicLineages.ComputabilityKnowledge.OracleDecoderDefinitions
public import LogicLineages.ComputabilityKnowledge.OracleDerivationDefinitions
public import Mathlib.Computability.RecursiveIn

@[expose] public section
/-! Literal finite numeric certificates and a terminating verifier for TOTAL
oracles. Eager evaluation of g(nodeInput i) is intentional and only justified
on this total-oracle domain. Previous-table entries are data, not assumptions. -/
namespace LogicLineages.ComputabilityKnowledge.OracleCertificate

open OracleProgram OracleDecoder OracleDerivation

def nodeData (index : Nat) : Nat := (index - 1).unpair.2
def nodeCode (index : Nat) : Nat := (nodeData index).unpair.1
def nodeInput (index : Nat) : Nat := (nodeData index).unpair.2.unpair.1
def nodeOutput (index : Nat) : Nat := (nodeData index).unpair.2.unpair.2.unpair.1
def nodeFuel (index : Nat) : Nat := (nodeData index).unpair.2.unpair.2.unpair.2.unpair.1
def nodeChildren (index : Nat) : Option (List Nat) :=
  Encodable.decode (α := List Nat) (nodeData index).unpair.2.unpair.2.unpair.2.unpair.2

def packNode (code input output fuel : Nat) (children : List Nat) : Nat :=
  Nat.pair (children.foldr max 0 + 1)
    (Nat.pair code (Nat.pair input (Nat.pair output (Nat.pair fuel (Encodable.encode children))))) + 1

def childMatches (child code input : Nat) : Bool :=
  (nodeCode child == code) && (nodeInput child == input)

def ruleCheck (answer index : Nat) (children : List Nat) : Bool :=
  let code := nodeCode index
  let input := nodeInput index
  let output := nodeOutput index
  let payload := (code - 1).unpair.2
  let first := children.getD 0 0
  let second := children.getD 1 0
  match (code - 1).unpair.1 with
  | 0 => children.isEmpty &&
      (Nat.Partrec.Code.evaln (nodeFuel index) (Denumerable.ofNat Nat.Partrec.Code payload) input == some output)
  | 1 => children.isEmpty && (output == answer)
  | 2 => (children.length == 2) &&
      childMatches first payload.unpair.1 input && childMatches second payload.unpair.2 input &&
      (output == Nat.pair (nodeOutput first) (nodeOutput second))
  | 3 => (children.length == 2) &&
      childMatches first payload.unpair.2 input && childMatches second payload.unpair.1 (nodeOutput first) &&
      (output == nodeOutput second)
  | 4 =>
      if input.unpair.2 = 0 then
        (children.length == 1) && childMatches first payload.unpair.1 input.unpair.1 &&
          (output == nodeOutput first)
      else
        (children.length == 2) && childMatches first code (Nat.pair input.unpair.1 (input.unpair.2 - 1)) &&
          childMatches second payload.unpair.2 (Nat.pair input.unpair.1 (Nat.pair (input.unpair.2 - 1) (nodeOutput first))) &&
          (output == nodeOutput second)
  | 5 => (children.length == output + 1) &&
      (List.range children.length).all (fun j =>
        childMatches (children.getD j 0) payload (Nat.pair input j) &&
          if j = output then nodeOutput (children.getD j 0) == 0 else !(nodeOutput (children.getD j 0) == 0))
  | _ => false

def certificateStep (answer index : Nat) (previous : List Bool) : Bool :=
  match nodeChildren index with
  | none => false
  | some children =>
      decide (0 < index) && validIndex (nodeCode index) &&
        children.all (fun child => decide (child < index) && previous.getD child false) &&
        ruleCheck answer index children

def certificateTable (g : Nat → Nat) : Nat → List Bool
  | 0 => []
  | n + 1 =>
      let previous := certificateTable g n
      previous ++ [certificateStep (g (nodeInput n)) n previous]

def validCertificate (g : Nat → Nat) (index : Nat) : Bool :=
  (certificateTable g (index + 1)).getD index false

def certificateFlag (g : Nat → Nat) (index : Nat) : Nat :=
  if validCertificate g index then 1 else 0

end LogicLineages.ComputabilityKnowledge.OracleCertificate
