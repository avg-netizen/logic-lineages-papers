module

public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryDefinitions

@[expose] public section
/-! Literal contiguous-subtree specification for the finite preorder registry.
The intended transport uses actual list positions, not an abstract dependency
oracle. It is a supplier for a single shared U/u equation interpretation. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRSubtree
open GorbowPRProgram GorbowPRRegistry

def BlockAt {n : Nat} (p : Program n) (tag : Nat) (a : Packed) : Prop :=
  ∃ before after : List Packed,
    nodes p = before ++ nodes a.2 ++ after ∧ before.length = tag

end LogicLineages.ComputabilityKnowledge.GorbowPRSubtree
