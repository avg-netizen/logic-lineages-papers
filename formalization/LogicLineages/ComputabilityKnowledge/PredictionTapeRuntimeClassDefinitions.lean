module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeGameDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderDefinitions
@[expose] public section
/-! Paper14 E_f and T(p,f), for the explicit finite-table ordinary tape
numbering. WorstTime is the actual attained finite maximum of charged tape
runtime, and the comparison is strict with finitely many length exceptions.
Totality is required separately on every input, including below the cutoff. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClass

def EventualRuntime (code : Nat) (b : Nat → Nat) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∃ t, PredictionTapeRuntime.WorstTime code n t ∧ t < b n

def RuntimeClass (code : Nat) (b : Nat → Nat) : Prop :=
  PredictionTapeObservation.TotalBinary code ∧ EventualRuntime code b

def Threshold (p : PredictionGame.Policy) (b : Nat → Nat) : Prop :=
  ∀ (e : Nat) (he : PredictionTapeObservation.TotalBinary e), EventualRuntime e b →
    PredictionGame.Learns p (PredictionTapeObservation.policy e he)

end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClass
