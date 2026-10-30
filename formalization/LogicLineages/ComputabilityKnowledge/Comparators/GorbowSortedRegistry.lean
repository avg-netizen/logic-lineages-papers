module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistry
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRegistry
open GorbowRegistryTuple GorbowRegistryDecoder
open LogicLineages.ComputabilityKnowledge.GorbowSortedRegistry

def RelationDispatch : Prop := ∀ a b,
  relationProgram (header 1 0 [a])=GorbowSortedBooleanCode.sentenceCode a ∧
  relationProgram (header 1 1 [a])=GorbowSortedBooleanCode.fullTermCode a ∧
  relationProgram (header 1 2 [a])=GorbowSortedBooleanCode.arithmeticTermCode a ∧
  relationProgram (header 1 3 [a])=GorbowSortedSyntaxCode.isVariableCode a ∧
  relationProgram (header 2 0 [a,b])=GorbowSortedNamedCode.namedFormula a b

def FunctionDispatch : Prop := ∀ a b c,
  functionProgram (header 1 0 [a])=GorbowSortedBooleanCode.unaryNumber 6 a ∧
  functionProgram (header 2 0 [a,b])=GorbowSortedBooleanCode.binaryNumber 7 a b ∧
  functionProgram (header 2 1 [a,b])=GorbowSortedBooleanCode.binaryNumber 8 a b ∧
  functionProgram (header 2 2 [a,b])=GorbowSortedBooleanCode.binaryNumber 9 a b ∧
  functionProgram (header 2 3 [a,b])=(GorbowSortedNamedCode.allNumber a b).getD 0 ∧
  functionProgram (header 2 4 [a,b])=(GorbowSortedNamedCode.exNumber a b).getD 0 ∧
  functionProgram (header 3 0 [a,b,c])=(GorbowSortedNamedCode.instanceNumber a b c).getD 0

def MalformedDefaults : Prop :=
  (∀ code, decodeHeader code=none → relationProgram code=false ∧ functionProgram code=0) ∧
  (∀ arity tag args,
    ¬(arity=1 ∧ tag<4 ∧ args.length=1) → ¬(arity=2 ∧ tag=0 ∧ args.length=2) →
    relationProgram (header arity tag args)=false) ∧
  (∀ arity tag args,
    ¬(arity=1 ∧ tag=0 ∧ args.length=1) → ¬(arity=2 ∧ tag<5 ∧ args.length=2) →
    ¬(arity=3 ∧ tag=0 ∧ args.length=3) → functionProgram (header arity tag args)=0)

def UniformPrograms : Prop := Primrec relationProgram ∧ Primrec functionProgram

def Target : Prop := RelationDispatch ∧ FunctionDispatch ∧ MalformedDefaults ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRegistry
