module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgramDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgramTargets
open PredictionTapeAntiProgram PredictionTapeObservation PredictionGame

def UniformRawAntiProgram : Prop :=
  ∃ (forward : Nat → Nat) (reverse anti : Nat.Partrec.Code),
    Primrec forward ∧ Computable (compile forward reverse anti) ∧
    ∀ (p : Nat) (hp : TotalBinary p),
      ∃ he : TotalBinary (compile forward reverse anti p),
        policy (compile forward reverse anti p) he = antiEvader (policy p hp) ∧
        (∀ n, prediction (policy p hp) (policy (compile forward reverse anti p) he) n ≠
          evasion (policy p hp) (policy (compile forward reverse anti p) he) n) ∧
        ¬ Learns (policy p hp) (policy (compile forward reverse anti p) he)

end LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgramTargets
