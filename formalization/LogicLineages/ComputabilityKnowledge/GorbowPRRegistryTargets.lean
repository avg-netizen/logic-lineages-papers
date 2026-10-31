module

public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRRegistry.Targets
open GorbowPRProgram

def ExactNodes : Prop := ∀ n (p : Program n) (a : Packed), a ∈ nodes p ↔ Occurs a p

def RootTag : Prop := ∀ n (p : Program n), (nodes p)[0]? = some ⟨n,p⟩

def TaggedCoverage : Prop := ∀ n (p : Program n) (a : Packed),
  Occurs a p ↔ ∃ tag ∈ tags p, (nodes p)[tag]? = some a

def UniqueTags : Prop := ∀ n (p : Program n), (tags p).Nodup

def ExactDispatch : Prop := ∀ n (p : Program n) tag m (q : Program m)
    (args : List Nat) (h : args.length = m),
  (nodes p)[tag]? = some ⟨m,q⟩ → dispatch p tag args = some (evaluate q ⟨args,h⟩)

def InvalidTag : Prop := ∀ n (p : Program n) tag args,
  (nodes p).length ≤ tag → dispatch p tag args = none

def InvalidArity : Prop := ∀ n (p : Program n) tag m (q : Program m) args,
  (nodes p)[tag]? = some ⟨m,q⟩ → args.length ≠ m → dispatch p tag args = none

end LogicLineages.ComputabilityKnowledge.GorbowPRRegistry.Targets
