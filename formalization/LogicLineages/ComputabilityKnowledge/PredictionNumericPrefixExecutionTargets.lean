module
public import LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecutionDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecutionTargets
open Turing PredictionFiniteAlphabet PredictionNumericPrefix PredictionNumericPrefixExecution

def ExactPrefixTransitions : Prop :=
  ∀ (p : Table) (q : Nat) (word : List Nat), p.2.2.length ≤ q * width p →
    ∀ xs : List (Fin (width p)),
      Moves p q word (2 * word.length) (initial p q word xs) (prepared p word xs)

def ExactBodyEvaluation : Prop :=
  ∀ (p : Table) (q : Nat) (word : List Nat), p.2.2.length ≤ q * width p →
    TM0.Supports (PredictionFiniteAlphabet.machine p) {s | s < q} →
    ∀ x : TM0.Cfg (Fin (width p)) Nat, x.q < q →
      StateTransition.eval (TM0.step (PredictionNumericPrefix.machine p q word)) x =
        StateTransition.eval (TM0.step (PredictionFiniteAlphabet.machine p)) x

def ExactPrefixEvaluation : Prop :=
  ∀ (p : Table) (q : Nat) (word : List Nat), p.2.2.length ≤ q * width p →
    TM0.Supports (PredictionFiniteAlphabet.machine p) {s | s < q} →
    ∀ xs : List (Fin (width p)), p.2.1 < q →
      StateTransition.eval (TM0.step (PredictionNumericPrefix.machine p q word)) (initial p q word xs) =
        StateTransition.eval (TM0.step (PredictionFiniteAlphabet.machine p)) (prepared p word xs)

def EffectiveParameterFamily : Prop := ∀ (p : Table) (q : Nat), Primrec (parameterCode p q)

end LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecutionTargets
