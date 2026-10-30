module

public import LogicLineages.ComputabilityKnowledge.GorbowPACore

@[expose] public section
/-! Actual closed equality contexts for constructive Hilbert derivations.
No semantic completeness or truth-to-proof premise is used. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowClosedEquality
open GorbowSyntax

def liftClosedTerm (n : Nat) (t : Term 0) : Term n :=
  GorbowSubstitution.substitute (Fin.elim0 : Fin 0 → Term n) t

def instantiateTerm (f : Term 1) (t : Term 0) : Term 0 :=
  GorbowSubstitution.substitute (Fin.cases t Fin.elim0) f
end LogicLineages.ComputabilityKnowledge.GorbowClosedEquality
