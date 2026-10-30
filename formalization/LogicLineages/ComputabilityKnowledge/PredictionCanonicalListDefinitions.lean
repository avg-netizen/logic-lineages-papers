module

public import LogicLineages.ComputabilityKnowledge.PredictionLearning
public import Mathlib.Data.Nat.Nth

@[expose] public section
/-! Noncomputable structural part of paper 14, lem:list (lines 367–390).
Index 0 here is the source's first retained entry a₁. No oracle computation
of the selection is supplied by Nat.nth. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalList
open PredictionLearning

def codeAt (i : Nat) : Code := Denumerable.ofNat Code i

def TotalNat (c : Code) : Prop := ∀ n : Nat, ∃ v : Nat, v ∈ Nat.Partrec.Code.eval c n

def SameFunction (c d : Code) : Prop :=
  ∀ n : Nat, Nat.Partrec.Code.eval c n = Nat.Partrec.Code.eval d n

def Representative (i : Nat) : Prop :=
  TotalNat (codeAt i) ∧ ∀ j : Nat, j < i → ¬ SameFunction (codeAt j) (codeAt i)

noncomputable def canonicalIndex (n : Nat) : Nat := Nat.nth Representative n

noncomputable def canonicalCode (n : Nat) : Code := codeAt (canonicalIndex n)

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalList
