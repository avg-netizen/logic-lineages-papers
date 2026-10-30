module

public import LogicLineages.ComputabilityKnowledge.GorbowTermShiftCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowLiftedDictionary
open GorbowSyntax GorbowSyntaxValidation GorbowTermShiftCode

def liftN {n m : Nat} (σ : Fin n → Term m) : (b : Nat) → Fin (n+b) → Term (m+b)
  | 0 => σ
  | b+1 => GorbowFormulaSubstitution.liftSubstitute (liftN σ b)

def dictionary {n m : Nat} (σ : Fin n → Term m) : List (List Nat) :=
  List.ofFn (fun i => GorbowTermPrefixCode.encode (σ i))

def dictionaryValid (n m : Nat) (dict : List (List Nat)) : Bool :=
  decide (dict.length = n) && dict.all (fun raw => validTerm m raw)

def liftedCode (m b : Nat) (dict : List (List Nat)) (i : Nat) : List Nat :=
  if i < b then [0,i] else shiftRaw m b (dict.getD (i-b) [])
end LogicLineages.ComputabilityKnowledge.GorbowLiftedDictionary
