module

public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRSubtree.Targets
open GorbowPRProgram GorbowPRRegistry

def NodeBlocks : Prop := ∀ n (p : Program n) (tag : Nat) (a : Packed),
  (nodes p)[tag]? = some a → BlockAt p tag a

def LookupTransport : Prop := ∀ n (p : Program n) (tag : Nat) (a : Packed) (localTag : Nat) (b : Packed),
  (nodes p)[tag]? = some a → (nodes a.2)[localTag]? = some b →
    (nodes p)[tag + localTag]? = some b

end LogicLineages.ComputabilityKnowledge.GorbowPRSubtree.Targets
