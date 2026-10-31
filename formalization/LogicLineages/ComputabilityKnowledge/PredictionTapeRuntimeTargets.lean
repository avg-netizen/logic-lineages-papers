module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntime.Targets

def RuntimeThreshold : Prop := ∀ (code : Nat) (xs : List Bool) (t : Nat),
  Runtime code xs t ↔ ∀ fuel, Successful code xs fuel ↔ t ≤ fuel

def WorstTimeThreshold : Prop := ∀ (code n t : Nat),
  WorstTime code n t ↔ ∀ fuel, (∀ xs : List Bool, xs.length = n → Successful code xs fuel) ↔ t ≤ fuel

def WorstTimeDomain : Prop := ∀ (code n : Nat),
  (∃ t, WorstTime code n t) ↔ ∀ xs : List Bool, xs.length = n → ∃ fuel, Successful code xs fuel

/-- Strict comparison, including budgets zero and one and empty histories.
The minus one is necessary because runtime includes the halt observation. -/
def StrictBudgetCalibration : Prop := ∀ (code n b : Nat),
  (∃ t, WorstTime code n t ∧ t < b) ↔
    ∀ xs : List Bool, xs.length = n → ∃ d, PredictionFiniteAlphabet.simulate code (b-1) xs = some d

def TotalBinaryWorstExists : Prop := ∀ (code : Nat), PredictionTapeObservation.TotalBinary code →
  ∀ n, ∃ t, WorstTime code n t

def ExactEvaderRuntime : Prop := ∀ (k : Nat) (xs : List Bool),
  Runtime (evaderCode k) xs (min k xs.length + 2)

def ExactEvaderWorstTime : Prop := ∀ k n, WorstTime (evaderCode k) n (min k n + 2)

def EventualEvaderStrictBound : Prop := ∀ k, ∃ N, ∀ n, N ≤ n →
  ∃ t, WorstTime (evaderCode k) n t ∧ t < n+1
end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntime.Targets
