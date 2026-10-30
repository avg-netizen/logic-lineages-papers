module

public import LogicLineages.ComputabilityKnowledge.GorbowLiftedDictionary

@[expose] public section

/-! Exact repeated lifting of the accepted substitution, including empty
contexts/dictionaries. No arbitrary malformed-state depth assumption. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowLiftedDictionary
open GorbowSyntax GorbowTermShiftCode
open LogicLineages.ComputabilityKnowledge.GorbowLiftedDictionary

def BoundIndex : Prop := ∀ (n m b : Nat) (σ : Fin n → Term m) (i : Fin (n+b))
  (h : i.val < b), liftN σ b i = Term.var ⟨i.val, Nat.lt_of_lt_of_le h (Nat.le_add_left b m)⟩

def FreeIndex : Prop := ∀ (n m b : Nat) (σ : Fin n → Term m) (i : Fin (n+b))
  (h : b ≤ i.val), liftN σ b i = shiftTerm b (σ ⟨i.val-b, by omega⟩)

def DictionaryCalibration : Prop := ∀ (n m : Nat) (σ : Fin n → Term m),
  (dictionary σ).length = n ∧ dictionaryValid n m (dictionary σ) = true ∧
  ∀ i : Fin n, (dictionary σ).getD i.val [] = GorbowTermPrefixCode.encode (σ i)

def ExactDictionaryDomain : Prop := ∀ n m dict, dictionaryValid n m dict = true ↔
  ∃ σ : Fin n → Term m, dict = dictionary σ

def LiftedCodeCalibration : Prop := ∀ (n m b : Nat) (σ : Fin n → Term m) (i : Fin (n+b)),
  liftedCode m b (dictionary σ) i.val = GorbowTermPrefixCode.encode (liftN σ b i)

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat × List (List Nat) => dictionaryValid p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List (List Nat) × Nat => liftedCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def Target : Prop := BoundIndex ∧ FreeIndex ∧ DictionaryCalibration ∧ ExactDictionaryDomain ∧ LiftedCodeCalibration ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowLiftedDictionary
