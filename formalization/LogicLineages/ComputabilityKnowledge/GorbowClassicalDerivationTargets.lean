module

public import LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation.Targets
open GorbowSyntax GorbowTheoryProof

def Explosion : Prop := ∀ (A : Sentence → Prop) (p q : Sentence),
  Derivation A p → Derivation A (.neg p) → Nonempty (Derivation A q)

def ClosedReductio : Prop := ∀ (A : Sentence → Prop) (p : Sentence),
  Derivation (contradictionBranch A p) p → Nonempty (Derivation A p)

def DoubleNegationElimination : Prop := ∀ (A : Sentence → Prop) (p : Sentence),
  Derivation A (.neg (.neg p)) → Nonempty (Derivation A p)

def ModusTollens : Prop := ∀ (A : Sentence → Prop) (p q : Sentence),
  Derivation A (.imp p q) → Derivation A (.neg q) → Nonempty (Derivation A (.neg p))

end LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation.Targets
