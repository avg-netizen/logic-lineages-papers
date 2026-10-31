module

public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryDefinitions

@[expose] public section
/-! Concrete child-address arithmetic in the finite preorder registry.
These offsets are needed to compile actual uniform defining equations; they
are not assumed lookup oracles and do not change the arithmetic Base. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRChildTags
open GorbowPRProgram GorbowPRRegistry

def argumentTag {m n : Nat} (f : Program n) (g : Fin n → Program m) (i : Fin n) : Nat :=
  1 + (nodes f).length + ((List.ofFn fun j => nodes (g j)).take i.val).flatten.length

def stepTag {n : Nat} (f : Program n) : Nat := 1 + (nodes f).length

end LogicLineages.ComputabilityKnowledge.GorbowPRChildTags
