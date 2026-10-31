module
public import LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecution
open Turing PredictionFiniteAlphabet PredictionNumericPrefix

inductive Moves (p : Table) (q : Nat) (word : List Nat) :
    Nat → TM0.Cfg (Fin (width p)) Nat → TM0.Cfg (Fin (width p)) Nat → Prop
  | refl (x) : Moves p q word 0 x x
  | next {n x y z} : TM0.step (PredictionNumericPrefix.machine p q word) x = some y →
      Moves p q word n y z → Moves p q word (n + 1) x z

def initial (p : Table) (q : Nat) (word : List Nat) (xs : List (Fin (width p))) :
    TM0.Cfg (Fin (width p)) Nat := ⟨entryState p q word.length, Tape.mk₁ xs⟩

def prepared (p : Table) (word : List Nat) (xs : List (Fin (width p))) :
    TM0.Cfg (Fin (width p)) Nat := ⟨p.2.1, Tape.mk₁ (word.map (symbol p) ++ xs)⟩

def parameterCode (p : Table) (q e : Nat) : Nat :=
  PredictionNumericPrefix.code p q (PredictionBinaryParameterLayout.numericWord e)

end LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecution
