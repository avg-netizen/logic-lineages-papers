module

public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistry

@[expose] public section
/-! A concrete padding root for the specific source U/u dispatcher programs.
All low-tag registry nodes have high arity. This preserves room for the
existing named source headers without changing any accepted old ground.
AST existence below is extensional, not an executable extraction compiler.
No old/new full-language interpretation or source Base identity is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding
open GorbowPRProgram GorbowPRRegistry

abbrev dummy : Program 4 := .projection 0

def wrapper (p : Program 1) : Program 4 := .composition p (fun _ => dummy)

def arguments (pF pR : Program 1) (i : Fin 5) : Program 4 :=
  if i.val = 3 then wrapper pF else if i.val = 4 then wrapper pR else dummy

def root (pF pR : Program 1) : Program 4 :=
  .composition (.projection (0 : Fin 5)) (arguments pF pR)

def paddingPrefix (pF pR : Program 1) : List Packed :=
  [⟨4,root pF pR⟩, ⟨5,.projection 0⟩, ⟨4,dummy⟩, ⟨4,dummy⟩, ⟨4,dummy⟩, ⟨4,wrapper pF⟩]

def middle (pR : Program 1) : List Packed := [⟨4,dummy⟩, ⟨4,wrapper pR⟩]

def functionTag : Nat := 6

def relationTag (pF : Program 1) : Nat := 8 + (nodes pF).length

def functionNames : List (Nat × Nat) :=
  [(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)]

def relationNames : List (Nat × Nat) := [(1,0),(1,1),(1,2),(1,3),(2,0)]

def sourceFunction : Nat → Nat := GorbowDiagonalRegistry.functionProgram

def sourceRelationValue (code : Nat) : Nat :=
  if GorbowSortedRegistry.relationProgram code then 1 else 0

end LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPadding
