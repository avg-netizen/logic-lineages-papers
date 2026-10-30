module

public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode
public import LogicLineages.ComputabilityKnowledge.GorbowPACore
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowInstanceCode
open GorbowCodeConstructors

def variableDictionary (n offset : Nat) : List (List Nat) :=
  (List.range n).map (fun i => variableCode (i+offset))

def instanceCode (n : Nat) (raw termRaw : List Nat) : Option (List Nat) :=
  GorbowSubstitutionCode.substituteFormulaCode (n+1) n (termRaw :: variableDictionary n 0) raw

def weakeningCode (n : Nat) (raw : List Nat) : Option (List Nat) :=
  GorbowSubstitutionCode.substituteFormulaCode n (n+1) (variableDictionary n 1) raw

def successorCode (n : Nat) (raw : List Nat) : Option (List Nat) :=
  GorbowSubstitutionCode.substituteFormulaCode (n+1) (n+1) ([2,0,0] :: variableDictionary n 1) raw

def inductionCode (n : Nat) (raw : List Nat) : Option (List Nat) := do
  let base ← instanceCode n raw [1]
  let next ← successorCode n raw
  some (binary 7 base (binary 7 (unary 10 (binary 7 raw next)) (unary 10 raw)))
end LogicLineages.ComputabilityKnowledge.GorbowInstanceCode
