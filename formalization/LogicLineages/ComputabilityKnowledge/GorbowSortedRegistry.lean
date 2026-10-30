module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCode
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevision

@[expose] public section

/-! Concrete sorted syntax registry for the source U/u convention. Header
arity/tag namespaces for U and u are distinct. This is a fresh ground, not a
change to any accepted legacy interpretation and not a Base representation
or derivability theorem. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedRegistry
open GorbowRegistryDecoder GorbowSortedSyntaxCode

def relationProgram (code : Nat) : Bool :=
  match decodeHeader code with
  | none => false
  | some (arity,tag,args) =>
    if arity=1 ∧ tag=0 ∧ args.length=1 then GorbowSortedBooleanCode.sentenceCode (args.getD 0 0)
    else if arity=1 ∧ tag=1 ∧ args.length=1 then GorbowSortedBooleanCode.fullTermCode (args.getD 0 0)
    else if arity=1 ∧ tag=2 ∧ args.length=1 then GorbowSortedBooleanCode.arithmeticTermCode (args.getD 0 0)
    else if arity=1 ∧ tag=3 ∧ args.length=1 then isVariableCode (args.getD 0 0)
    else if arity=2 ∧ tag=0 ∧ args.length=2 then GorbowSortedNamedCode.namedFormula (args.getD 0 0) (args.getD 1 0)
    else false

def functionProgram (code : Nat) : Nat :=
  match decodeHeader code with
  | none => 0
  | some (arity,tag,args) =>
    if arity=1 ∧ tag=0 ∧ args.length=1 then GorbowSortedBooleanCode.unaryNumber 6 (args.getD 0 0)
    else if arity=2 ∧ tag<3 ∧ args.length=2 then GorbowSortedBooleanCode.binaryNumber (tag+7) (args.getD 0 0) (args.getD 1 0)
    else if arity=2 ∧ tag=3 ∧ args.length=2 then (GorbowSortedNamedCode.allNumber (args.getD 0 0) (args.getD 1 0)).getD 0
    else if arity=2 ∧ tag=4 ∧ args.length=2 then (GorbowSortedNamedCode.exNumber (args.getD 0 0) (args.getD 1 0)).getD 0
    else if arity=3 ∧ tag=0 ∧ args.length=3 then (GorbowSortedNamedCode.instanceNumber (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)).getD 0
    else 0

def ground : GorbowSortedRevision.Ground := ⟨fun code => relationProgram code=true,functionProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedRegistry
