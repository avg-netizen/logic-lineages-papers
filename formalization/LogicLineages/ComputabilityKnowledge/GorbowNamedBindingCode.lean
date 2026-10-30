module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedBinding
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode
public import LogicLineages.ComputabilityKnowledge.GorbowSupportCode
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

@[expose] public section

/-! Explicit-context literal code programs for arbitrary-name binding. The
select guard requires the exact names [v], not merely support cardinality one.
No inferred raw ambient bound or ambient-zero decoding is asserted here. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedBindingCode
open GorbowCodeConstructors

def bindDictionaryCode (n v : Nat) : List (List Nat) :=
  (List.range n).map (fun i => if i=v then variableCode 0 else variableCode (i+1))
def selectDictionaryCode (n v : Nat) : List (List Nat) :=
  (List.range n).map (fun i => if i=v then variableCode 0 else [1])

def bindCode (tag n v : Nat) (raw : List Nat) : Option (List Nat) :=
  if v<n then (GorbowSubstitutionCode.substituteFormulaCode n (n+1) (bindDictionaryCode n v) raw).map (unary tag) else none

def bindAllCode (n v : Nat) (raw : List Nat) : Option (List Nat) := bindCode 10 n v raw
def bindExCode (n v : Nat) (raw : List Nat) : Option (List Nat) := bindCode 11 n v raw

def selectCode (n v : Nat) (raw : List Nat) : Option (List Nat) :=
  if v<n ∧ GorbowSupportCode.formulaNames n raw=some [v] then
    GorbowSubstitutionCode.substituteFormulaCode n 1 (selectDictionaryCode n v) raw
  else none
end LogicLineages.ComputabilityKnowledge.GorbowNamedBindingCode
