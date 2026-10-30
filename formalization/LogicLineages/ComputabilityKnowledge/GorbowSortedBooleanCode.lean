module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode
public import LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowClosedTermCode

@[expose] public section

/-! Sorted Boolean raw syntax builders and exact sentence/closed-term guards.
These are syntax operations only; they do not transport legacy truth models. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCode
open GorbowSortedSyntaxCode

def unaryNumber (tag code : Nat) : Nat :=
  if code%2=0 then tagFormula (GorbowBooleanRegistry.unaryNumber tag (code/2)) else 0
def binaryNumber (tag a b : Nat) : Nat :=
  if a%2=0 ∧ b%2=0 then tagFormula (GorbowBooleanRegistry.binaryNumber tag (a/2) (b/2)) else 0
def sentenceCode (code : Nat) : Bool :=
  decide (code%2=0) && GorbowBooleanRegistry.sentenceCode (code/2)
def fullTermCode (code : Nat) : Bool :=
  decide (code%2=1) && GorbowClosedTermCode.fullTermCode (code/2)
def arithmeticTermCode (code : Nat) : Bool :=
  decide (code%2=1) && GorbowClosedTermCode.arithmeticTermCode (code/2)
end LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCode
