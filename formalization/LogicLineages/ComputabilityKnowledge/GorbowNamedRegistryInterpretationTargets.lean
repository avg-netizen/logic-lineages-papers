module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowSourceRegistryPadding List.Vector

def InternalHeader : Prop := ∀ (pF pR : Program 1) (tag : Nat) m (q : Program m)
    (args : List Nat) (h : args.length = m),
  (nodes (root pF pR))[tag]? = some ⟨m,q⟩ →
    functionProgram pF pR (GorbowRegistryTuple.header m tag args) = evaluate q ⟨args,h⟩

def InternalTerm : Prop := ∀ ctx (pF pR : Program 1) (tag : Nat) m (q : Program m)
    (args : List.Vector (Term ctx) m) I (rho : Fin ctx → Nat),
  (nodes (root pF pR))[tag]? = some ⟨m,q⟩ →
    (GorbowPRDefiningEquations.call tag args).realize (interpretation pF pR I) rho =
      evaluate q (args.map fun t => t.realize (interpretation pF pR I) rho)

def NamedFunction : Prop := ∀ (pF pR : Program 1) name, name ∈ functionNames →
  ∀ args : List Nat, args.length = name.1 →
    functionProgram pF pR (GorbowRegistryTuple.header name.1 name.2 args) =
      evaluate pF (GorbowRegistryTuple.header name.1 name.2 args ::ᵥ List.Vector.nil)

def NamedRelation : Prop := ∀ (pF pR : Program 1) name, name ∈ relationNames →
  ∀ args : List Nat, args.length = name.1 →
    (relationProgram pF pR (GorbowRegistryTuple.header name.1 name.2 args) = true ↔
      evaluate pR (GorbowRegistryTuple.header name.1 name.2 args ::ᵥ List.Vector.nil) = 1)

def SpecificNamedBridge : Prop := ∃ pF pR : Program 1,
  (∀ name ∈ functionNames, ∀ args : List Nat, args.length = name.1 →
    functionProgram pF pR (GorbowRegistryTuple.header name.1 name.2 args) =
      sourceFunction (GorbowRegistryTuple.header name.1 name.2 args)) ∧
  (∀ name ∈ relationNames, ∀ args : List Nat, args.length = name.1 →
    relationProgram pF pR (GorbowRegistryTuple.header name.1 name.2 args) =
      GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header name.1 name.2 args))

end LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation.Targets
