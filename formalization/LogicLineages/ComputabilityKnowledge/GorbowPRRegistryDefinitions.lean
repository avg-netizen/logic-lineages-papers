module

public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
/-! A finite executable registry of primitive-recursive AST occurrences.
Tags are list positions, not extensional functions or assumed code oracles.
Duplicate subprograms may occur at distinct tags. No U/u defining theory,
source Base, arithmetized provability or paper-12 conclusion is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRRegistry
open GorbowPRProgram

abbrev Packed := Sigma Program

def nodes : {n : Nat} → Program n → List Packed
  | _, .zero => [⟨0,.zero⟩]
  | _, .succ => [⟨1,.succ⟩]
  | _, .projection i => [⟨_,.projection i⟩]
  | _, .composition f g =>
      ⟨_,.composition f g⟩ :: (nodes f ++ (List.ofFn fun i => nodes (g i)).flatten)
  | _, .recursion f g => ⟨_,.recursion f g⟩ :: (nodes f ++ nodes g)

inductive Occurs (a : Packed) : {n : Nat} → Program n → Prop where
  | here {n} (p : Program n) : a = ⟨n,p⟩ → Occurs a p
  | compositionFunction {m n} (f : Program n) (g : Fin n → Program m) :
      Occurs a f → Occurs a (.composition f g)
  | compositionArgument {m n} (f : Program n) (g : Fin n → Program m) (i : Fin n) :
      Occurs a (g i) → Occurs a (.composition f g)
  | recursionBase {n} (f : Program n) (g : Program (n+2)) :
      Occurs a f → Occurs a (.recursion f g)
  | recursionStep {n} (f : Program n) (g : Program (n+2)) :
      Occurs a g → Occurs a (.recursion f g)

def tags {n : Nat} (p : Program n) : List Nat := List.range (nodes p).length

def dispatch {n : Nat} (p : Program n) (tag : Nat) (args : List Nat) : Option Nat := do
  let entry ← (nodes p)[tag]?
  if h : args.length = entry.1 then
    some (evaluate entry.2 ⟨args,h⟩)
  else none

end LogicLineages.ComputabilityKnowledge.GorbowPRRegistry
