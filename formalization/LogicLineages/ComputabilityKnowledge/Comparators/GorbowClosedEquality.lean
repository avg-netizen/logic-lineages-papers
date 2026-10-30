module

public import LogicLineages.ComputabilityKnowledge.GorbowClosedEquality

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedEquality
open GorbowSyntax GorbowPACore GorbowStandardInstances
open LogicLineages.ComputabilityKnowledge.GorbowClosedEquality

def ClosedTransport : Prop := ∀ n (t : Term 0) (σ : Fin n → Term 0),
  GorbowSubstitution.substitute σ (liftClosedTerm n t)=t

def Reflexivity : Prop := ∀ t : Term 0, Nonempty (Proof (.equal t t))

def FormulaTransport : Prop := ∀ (φ : Formula 1) (t u : Term 0),
  Proof (.equal t u) → Proof (instantiate φ t) → Nonempty (Proof (instantiate φ u))

def Symmetry : Prop := ∀ t u : Term 0, Proof (.equal t u) → Nonempty (Proof (.equal u t))
def Transitivity : Prop := ∀ t u v : Term 0,
  Proof (.equal t u) → Proof (.equal u v) → Nonempty (Proof (.equal t v))
def TermCongruence : Prop := ∀ (f : Term 1) (t u : Term 0),
  Proof (.equal t u) → Nonempty (Proof (.equal (instantiateTerm f t) (instantiateTerm f u)))

def Target : Prop := ClosedTransport ∧ Reflexivity ∧ FormulaTransport ∧ Symmetry ∧ Transitivity ∧ TermCongruence
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedEquality
