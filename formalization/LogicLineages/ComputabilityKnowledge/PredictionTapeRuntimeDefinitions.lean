module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationProof
public import LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbeddingProof
public import Mathlib.Data.Nat.Find
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntime

/-- Actual numerical tape simulation succeeds within this fuel, counting the
terminal halt observation. No `evaln` clock is used. -/
def Successful (code : Nat) (xs : List Bool) (fuel : Nat) : Prop :=
  ∃ d, PredictionFiniteAlphabet.simulate code fuel xs = some d

/-- Partial runtime relation: the least successful fuel. Divergent inputs have
no runtime, rather than a fabricated default value. -/
def Runtime (code : Nat) (xs : List Bool) (t : Nat) : Prop :=
  Successful code xs t ∧ ∀ fuel, fuel < t → ¬ Successful code xs fuel

/-- Exact finite maximum, with an attaining input. This relation has a value
only when every length-n input halts; it assigns no default on nontermination. -/
def WorstTime (code n t : Nat) : Prop :=
  (∀ xs : List Bool, xs.length = n → ∃ s, Runtime code xs s ∧ s ≤ t) ∧
  ∃ xs : List Bool, xs.length = n ∧ Runtime code xs t

/-- Explicit finite enumeration, used only to establish the exact domain of
the finite maximum. -/
def histories : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (histories n).map (false :: ·) ++ (histories n).map (true :: ·)

def evaderCode (k : Nat) : Nat := PredictionAlphabetEmbedding.liftCode (PredictionTapeCode.code k)
end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntime
