module

public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitution

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowHeaderSubstitution
open GorbowSyntax GorbowRegistryTuple GorbowSubstitution

def Numerals : Prop := ∀ m n (σ : Fin m → Term n) k,
  substitute σ (Term.numeral k)=Term.numeral k

def Pairs : Prop := ∀ m n (σ : Fin m → Term n) (a b : Term m),
  substitute σ (pairTerm a b)=pairTerm (substitute σ a) (substitute σ b)

def Tuples : Prop := ∀ m n (σ : Fin m → Term n) (as : List (Term m)),
  substitute σ (tupleTerm as)=tupleTerm (as.map (substitute σ))

def Headers : Prop := ∀ m n (σ : Fin m → Term n) arity tag (as : List (Term m)),
  substitute σ (headerTerm arity tag as)=headerTerm arity tag (as.map (substitute σ))

def Target : Prop := Numerals ∧ Pairs ∧ Tuples ∧ Headers
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowHeaderSubstitution
