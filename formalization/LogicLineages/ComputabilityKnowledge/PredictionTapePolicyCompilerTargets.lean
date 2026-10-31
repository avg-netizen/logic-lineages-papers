module
public import LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerTargets
open PredictionTapePolicyCompiler

def EffectivePolicyTransport : Prop :=
  ∃ f : Nat → Nat, Primrec f ∧ ∀ (c : Nat.Partrec.Code) (hc : PredictionLearning.TotalBinary c),
    ∃ ht : PredictionTapeObservation.TotalBinary (transport f c),
      PredictionTapeObservation.policy (transport f c) ht = PredictionLearning.policy c hc

def UniformSelfHistoryTapeProgram : Prop :=
  ∀ R : PredictionUniformHistory.ParameterRule,
    Computable (fun q : Nat × List Bool × List Bool => R q.1 q.2.1 q.2.2) →
    ∃ g : Nat → Nat, Computable g ∧ ∀ z : Nat,
      ∃ hp : PredictionTapeObservation.TotalBinary (g z),
        PredictionTapeObservation.policy (g z) hp = PredictionSelfHistory.selfPolicy (R z)

end LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerTargets
