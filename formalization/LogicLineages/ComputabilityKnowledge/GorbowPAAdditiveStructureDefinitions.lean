module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof

@[expose] public section
/-! Genuine quantified PA(L) arithmetic needed for finite-range elimination
and internal beta-trace proofs. These are formulas to derive, never extra
axioms or assertions inferred from standard-model validity. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure
open GorbowSyntax

def predecessor : Sentence :=
  .all (.disj (.equal (.var 0) .zero)
    (.ex (.equal (.var 1) (.succ (.var 0)))))

def leftZero : Sentence := .all (.equal (.add .zero (.var 0)) (.var 0))

/-- Bound context [y,x]. -/
def leftSuccessor : Sentence := .all (.all
  (.equal (.add (.succ (.var 1)) (.var 0)) (.succ (.add (.var 1) (.var 0)))))

/-- Bound context [z,y,x]. -/
def rightCancellation : Sentence := .all (.all (.all
  (.imp (.equal (.add (.var 2) (.var 0)) (.add (.var 1) (.var 0)))
    (.equal (.var 2) (.var 1)))))

end LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure
