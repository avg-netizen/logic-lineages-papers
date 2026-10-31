module

public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruence.Targets
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowPRDefiningEquations

def TermCongruence : Prop := ∀ (A : Sentence → Prop) n (t : Term n)
    (sigma tau : Fin n → Term 0),
  (∀ i, Nonempty (Derivation A (.equal (sigma i) (tau i)))) →
    Nonempty (Derivation A (.equal (substitute sigma t) (substitute tau t)))

def CallSubstitution : Prop := ∀ ctx out arity tag (args : List.Vector (Term ctx) arity)
    (sigma : Fin ctx → Term out),
  substitute sigma (call tag args) = call tag (args.map (substitute sigma))

def CallCongruence : Prop := ∀ (A : Sentence → Prop) arity tag
    (args others : List.Vector (Term 0) arity),
  (∀ i, Nonempty (Derivation A (.equal (args.get i) (others.get i)))) →
    Nonempty (Derivation A (.equal (call tag args) (call tag others)))

end LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruence.Targets
