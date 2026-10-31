module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputableDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputableTargets
open PredictionTapeRuntimeComputable PredictionTapeRuntime PredictionTapeObservation

def ExactFiniteTest : Prop := ∀ code n fuel,
  allHalting code n fuel = true ↔ ∀ xs : List Bool, xs.length=n → Successful code xs fuel

def EffectiveRuntimeSearch : Prop :=
  Primrec (fun z : Nat × Nat × Nat => allHalting z.1 z.2.1 z.2.2) ∧ Partrec₂ partialWorstTime

def ExactPartialRuntime : Prop := ∀ code n t,
  t ∈ partialWorstTime code n ↔ WorstTime code n t

def TotalProgramComputableRuntime : Prop := ∀ code : Nat, TotalBinary code →
  ∃ time : Nat → Nat, Computable time ∧ ∀ n, WorstTime code n (time n)

end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputableTargets
