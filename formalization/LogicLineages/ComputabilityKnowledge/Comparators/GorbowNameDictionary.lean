module

public import LogicLineages.ComputabilityKnowledge.GorbowNameDictionary

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNameDictionary
open GorbowSyntax GorbowFreeSupport GorbowFormulaSubstitution
open LogicLineages.ComputabilityKnowledge.GorbowNameDictionary

def Lookup : Prop := ∀ n m k (names : Fin n → Fin m), Function.Injective names →
  ∀ (values : Fin n → Term k) j, dictionary names values (names j)=values j

def UnusedZero : Prop := ∀ n m k (names : Fin n → Fin m) (values : Fin n → Term k) i,
  (¬ ∃ j, names j=i) → dictionary names values i=.zero

def PreciseSupport : Prop := ∀ n m (R : Formula m) (names : Fin n → Fin m),
  Function.Injective names → Covers R names →
  (formulaSupport R).card=n ∧ (∀ i : Fin m, i.val∈formulaSupport R ↔ ∃ j, names j=i)

def LiteralLocality : Prop := ∀ n m k (R : Formula m) (names : Fin n → Fin m),
  Function.Injective names → Covers R names → ∀ (values : Fin n → Term k) (σ : Fin m → Term k),
  (∀ j, σ (names j)=values j) →
  substituteFormula (dictionary names values) R=substituteFormula σ R

def Realization : Prop := ∀ n m k (R : Formula m) (names : Fin n → Fin m),
  Function.Injective names → Covers R names → ∀ (values : Fin n → Term k) I ρ v,
  (∀ j, v (names j)=(values j).realize I ρ) →
  ((substituteFormula (dictionary names values) R).realize I ρ ↔ R.realize I v)

def Target : Prop := Lookup ∧ UnusedZero ∧ PreciseSupport ∧ LiteralLocality ∧ Realization
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNameDictionary
