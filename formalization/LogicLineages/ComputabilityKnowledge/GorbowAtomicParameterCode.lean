module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCode

@[expose] public section
/-! Literal annotation dictionaries. First occurrence lookup is retained even
for duplicate names. Unused code slots contain the numeral of the tagged zero
term code; unused value slots contain the raw zero term, not that numeral. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicParameterCode
open GorbowSyntax GorbowCodeConstructors GorbowRegistryTermCode

def codeSlot (names : List Nat) (i : Nat) : List Nat :=
  let k := names.idxOf i
  if k<names.length then variableCode k else numeral (GorbowSortedSyntaxCode.termCode (.zero : Term 0))

def valueSlot (names : List Nat) (i : Nat) : List Nat :=
  let k := names.idxOf i
  if k<names.length then evaluationRaw (variableCode k) else [1]

def codeSlots (m : Nat) (names : List Nat) : List (List Nat) :=
  (List.range m).map (codeSlot names)

def valueSlots (m : Nat) (names : List Nat) : List (List Nat) :=
  (List.range m).map (valueSlot names)

def instanceRaw (m : Nat) (raw names : List Nat) : List Nat :=
  unary 5 (headerRaw 3 1 [numeral m,numeral (GorbowSortedSyntaxCode.formulaRawNumber raw),
    tupleRaw (codeSlots m names)])
end LogicLineages.ComputabilityKnowledge.GorbowAtomicParameterCode
