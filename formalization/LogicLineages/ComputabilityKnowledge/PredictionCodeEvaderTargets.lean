module

public import LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderTargets
open PredictionGame PredictionLearning PredictionUniformHistory PredictionCodeEvader

def CompletedCodeSpecification : Prop :=
  ∀ xs : List Bool,
    (completedCode xs = none ↔ ∀ b ∈ xs, b = true) ∧
    ∀ k : Nat, completedCode xs = some k ↔
      k < xs.length ∧ xs[k]? = some false ∧ ∀ i : Nat, i < k → xs[i]? = some true

def CompletedCodePermanent : Prop :=
  ∀ (xs ys : List Bool) (k : Nat), completedCode xs = some k → completedCode (xs ++ ys) = some k

def CompletedCodePrimitiveRecursive : Prop := Primrec completedCode

def CodeEvaderStream : Prop :=
  ∀ (k : Nat) (p : Policy) (n : Nat), evasion p (codePolicy k) n = decide (n < k) ∧
    completedCode (histories p (codePolicy k) n).evasions = if k < n then some k else none

def UniformCodeEvaderProgram : Prop :=
  ∃ u : Code, Computable (compileSelfHistory u) ∧ ∀ k : Nat,
    ∃ he : TotalBinary (compileSelfHistory u k), policy (compileSelfHistory u k) he = codePolicy k

def CompletedCodeActualStabilization : Prop :=
  ∀ p e : Policy,
    (∀ n : Nat, completedCode (histories p e n).evasions = none) ∨
      ∃ N k : Nat, ∀ n : Nat, N ≤ n → completedCode (histories p e n).evasions = some k

end LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderTargets
