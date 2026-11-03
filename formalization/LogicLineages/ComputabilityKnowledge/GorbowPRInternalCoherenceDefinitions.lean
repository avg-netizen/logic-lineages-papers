module

public import LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquationsDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryDefinitions

@[expose] public section
/-! Internal symbolic coherence for duplicate occurrences of the SAME finite
primitive-recursive AST. The conclusion is an actual full-language Hilbert
proof with arbitrary free arguments, not extensional equality in the standard
model. Recursive programs require the genuine object-language induction rule.
Original Base identification, arbitrary extensional program equivalence and
internal HB/Lob remain separate obligations. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence
open GorbowPRProgram GorbowPRRegistry

def duplicateRoot {n : Nat} (q : Program n) : Program n :=
  .composition (.projection (0 : Fin 2)) (fun _ : Fin 2 => q)

def leftTag : Nat := 2

def rightTag {n : Nat} (q : Program n) : Nat := 2 + (nodes q).length

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherence
