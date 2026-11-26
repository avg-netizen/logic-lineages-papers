module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSourceProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113 List.Vector
/-- The already chosen source root. No new registry or source tuple is built. -/
abbrev sourceRoot (pF pR : Program 1) (q : Program 5) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF q) pR
/-- Exact original rule 4 line, with original Line encoding, not a proof code. -/
def lineCode (sigma : Sentence) : Nat := Encodable.encode (GorbowTheoryChecker.axiomLine 0 sigma)
def arguments (c : Code) (fuel : Nat) (sigma : Sentence) : List.Vector Nat 3 :=
 Encodable.encode c ::ᵥ fuel ::ᵥ lineCode sigma ::ᵥ nil
/-- Actual installed defining-equation graph, retaining the evaluated output. -/
def graphEquation (tag : Nat) (x : Program 3) (c : Code) (fuel : Nat) (sigma : Sentence) : Sentence :=
 .equal (GorbowPRDefiningEquations.call tag
   ((arguments c fuel sigma).map (Term.numeral : Nat → Term 0)))
  (Term.numeral (evaluate (SaturatedAxiomLeaf.saturated x) (arguments c fuel sigma)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf
