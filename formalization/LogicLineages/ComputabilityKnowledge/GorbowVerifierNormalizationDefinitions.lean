module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalControlDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBDefinitions

@[expose] public section
/-! Canonical Boolean normalization tests equality to ONE, not nonzeroness.
It preserves the actual internal acceptance formula of a same-AST program
occurrence without assuming that program has internally Boolean outputs. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

def equalsOneStep : Program 2 :=
  .composition GorbowPRInternalControl.zeroTest (fun _ : Fin 1 => .projection (0 : Fin 2))

def equalsOne : Program 1 := .recursion .zero equalsOneStep

def normalize {n : Nat} (q : Program n) : Program n :=
  .composition equalsOne (fun _ : Fin 1 => q)

def booleanRange {n : Nat} (t : Term n) : Formula n :=
  .disj (.equal t .zero) (.equal t (Term.numeral 1))

end LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization
