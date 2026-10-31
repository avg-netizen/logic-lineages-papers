module

public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRChildTags.Targets
open GorbowPRProgram GorbowPRRegistry

def CompositionFunction : Prop := ∀ m n (f : Program n) (g : Fin n → Program m),
  (nodes (.composition f g))[1]? = some ⟨n,f⟩

def CompositionArgument : Prop := ∀ m n (f : Program n) (g : Fin n → Program m) (i : Fin n),
  (nodes (.composition f g))[argumentTag f g i]? = some ⟨m,g i⟩

def RecursionBase : Prop := ∀ n (f : Program n) (g : Program (n+2)),
  (nodes (.recursion f g))[1]? = some ⟨n,f⟩

def RecursionStep : Prop := ∀ n (f : Program n) (g : Program (n+2)),
  (nodes (.recursion f g))[stepTag f]? = some ⟨n+2,g⟩

end LogicLineages.ComputabilityKnowledge.GorbowPRChildTags.Targets
