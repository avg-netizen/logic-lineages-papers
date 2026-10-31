module
public import LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValuesDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValuesTargets
open PredictionSourceFiniteValues PredictionTapeObservation PredictionOriginalHardness

def WholeSourceFiniteValues : Prop :=
  ∀ g : Nat → Nat → Nat, CoversComputable g →
    ∀ (p : Nat) (hp : TotalBinary p), ∃ h : Nat, originalHeight g (policy p hp) = (h : WithTop Nat)

end LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValuesTargets
