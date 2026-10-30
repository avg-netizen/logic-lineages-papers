module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowHeaderSubstitution

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
open GorbowSyntax GorbowRegistryTuple GorbowSubstitution

theorem numerals : Comparators.GorbowHeaderSubstitution.Numerals := by
  intro m n σ k
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Term.succ ih

theorem pairs : Comparators.GorbowHeaderSubstitution.Pairs := by
  intro m n σ a b
  rfl

theorem tuples : Comparators.GorbowHeaderSubstitution.Tuples := by
  intro m n σ as
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [tupleTerm,substitute,pairTerm,List.map_cons,ih]

theorem headers : Comparators.GorbowHeaderSubstitution.Headers := by
  intro m n σ arity tag as
  unfold headerTerm
  rw [pairs,pairs,numerals,numerals,tuples]

theorem gorbowHeaderSubstitution : Comparators.GorbowHeaderSubstitution.Target :=
  ⟨numerals,pairs,tuples,headers⟩
end LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
