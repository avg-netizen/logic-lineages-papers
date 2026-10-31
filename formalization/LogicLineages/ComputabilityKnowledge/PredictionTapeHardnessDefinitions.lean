module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeFlipDefinitions
@[expose] public section
/-! Source paper14 prop:hardness, fixed-budget normal-form reduction in the
explicit ordinary finite-table tape numbering. The budget premise is exactly
eventual domination of the proved k-evader runtime min(k,n)+2. It is not a
hypothesis supplying a reduction, machine runtime, universal compiler or
oracle. Total predictor codes and their uniform computability are conclusions.
Full Turing-degree classification and portability to other numberings are
not asserted here. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeHardness

def DominatesCodeEvaders (b : Nat → Nat) : Prop :=
  ∀ k : Nat, ∃ N, ∀ n, N ≤ n → min k n + 2 < b n

end LogicLineages.ComputabilityKnowledge.PredictionTapeHardness
