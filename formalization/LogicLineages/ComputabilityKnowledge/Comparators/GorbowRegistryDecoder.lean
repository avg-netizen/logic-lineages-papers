module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDecoder
open GorbowRegistryTuple
open LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder

def PairExact : Prop := ∀ code a b, decodePair code = some (a,b) ↔ pair a b=code

def StepInvariant : Prop :=
  (∀ acc, tupleStep (some (0,acc))=some (0,acc)) ∧
  (∀ c acc next, tupleStep (some (c,acc))=some next →
    restore next.2 next.1=restore acc c ∧ (c=0 ∨ next.1<c))

def FuelSufficiency : Prop := ∀ xs acc fuel, tuple xs≤fuel →
  tupleStep^[fuel] (some (tuple xs,acc))=some (0,xs.reverse++acc)

def TupleExact : Prop := ∀ code xs, decodeTuple code=some xs ↔ tuple xs=code

def HeaderExact : Prop := ∀ code arity tag args,
  decodeHeader code=some (arity,tag,args) ↔ header arity tag args=code

def UniformPrograms : Prop := Primrec pairCandidates ∧ Primrec decodePair ∧ Primrec tupleStep ∧
  Primrec decodeTuple ∧ Primrec decodeHeader

def Target : Prop := PairExact ∧ StepInvariant ∧ FuelSufficiency ∧ TupleExact ∧ HeaderExact ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDecoder
