module

public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowProgramDiagram
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitution
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEquality
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaComposition

@[expose] public section
/-! A literal closed diagonal sentence for each ambient unary formula, in a
fresh concrete registry-ground diagram theory. This is not uniform graph
representability, an adequate source Base, or the self-referential DCB theory.
No previous registry interpretation is identified with this fresh one. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentence
open GorbowSyntax

def deltaTerm {n : Nat} (t : Term n) : Term n :=
  .universalFunction (GorbowRegistryTuple.headerTerm 1 2 [t])

def theta (φ : Formula 1) : Formula 1 :=
  GorbowFormulaSubstitution.substituteFormula (fun _ : Fin 1 => deltaTerm (.var 0)) φ

def diagonal (φ : Formula 1) : Sentence :=
  GorbowSortedSelfApplication.selfInstance (theta φ)

def theoryProgram : List Nat → Bool := GorbowProgramDiagram.axiomProgram
  GorbowSortedRegistry.relationProgram GorbowDiagonalRegistry.functionProgram

def Theory : Sentence → Prop := GorbowProgramDiagram.Theory
  GorbowSortedRegistry.relationProgram GorbowDiagonalRegistry.functionProgram
end LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentence
