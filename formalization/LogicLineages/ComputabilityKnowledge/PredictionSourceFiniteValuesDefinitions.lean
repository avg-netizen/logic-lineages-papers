module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputableDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgramDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValues

/-- Coverage only: the source permits a noncomputable listing of total functions. -/
def CoversComputable (g : Nat → Nat → Nat) : Prop :=
  ∀ f : Nat → Nat, Computable f → ∃ i : Nat, ∀ n : Nat, g i n = f n

end LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValues
