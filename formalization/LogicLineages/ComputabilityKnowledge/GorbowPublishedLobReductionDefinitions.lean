module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBDefinitions

@[expose] public section
/-! The actual published D and its literal proof predicate, with an explicit
Lob diagonal and the exact internal derivability instances the argument uses.
The instances below are formulas, not axioms added to D. Their derivability
remains an explicit premise of the reduction and a separate arithmetic task. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
open GorbowPublishedDCB

/-- The free variable denotes the code of the candidate diagonal sentence. -/
def provabilityTemplate (pF : Program 1) (c : Code) : Formula 1 :=
  applyProv pF c (GorbowBooleanTruth.binaryCodeTerm 0
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))) (.var 0))

def lobTemplate (pF : Program 1) (c : Code) (theta : Sentence) : Formula 1 :=
  .imp (provabilityTemplate pF c) (GorbowTheoryProof.weakenClosed 1 theta)

def delta (pF : Program 1) (c : Code) (theta : Sentence) : Sentence :=
  GorbowDiagonalSentence.diagonal (lobTemplate pF c theta)

def hb2 (pF : Program 1) (c : Code) (sigma tau : Sentence) : Sentence :=
  .imp (prD pF c (.imp sigma tau)) (.imp (prD pF c sigma) (prD pF c tau))

def hb3 (pF : Program 1) (c : Code) (sigma : Sentence) : Sentence :=
  .imp (prD pF c sigma) (prD pF c (prD pF c sigma))

end LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction
