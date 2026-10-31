module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundProgramsDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundProgramsTargets
open PredictionOriginalBoundPrograms

def UniformOrdinaryBounds : Prop :=
  ∀ g : Nat → Nat → Nat, Computable₂ g →
    ∃ u : Nat.Partrec.Code, Primrec (compile u) ∧ CompilerSemantics u g

def ExactTotalBoundValues : Prop :=
  ∀ (u : Nat.Partrec.Code) (g : Nat → Nat → Nat), CompilerSemantics u g →
    ∀ m : Nat, PredictionCanonicalList.TotalNat (compile u m) ∧
      ∀ n : Nat, PredictionMaximum.evalValue (compile u m) n = PredictionOriginalBounds.levelBound g m n

end LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundProgramsTargets
