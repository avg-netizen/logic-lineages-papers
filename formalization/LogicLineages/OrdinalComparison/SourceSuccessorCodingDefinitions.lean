module

public import LogicLineages.OrdinalComparison.SourceApplicativeDefinitions
public import LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibration

@[expose] public section
/-! The numeric observation is defined from the actual finite-head collapse,
not from the intended Phi closed form. Source addition/eraser realization is
not part of this arithmetic coding stage. -/
namespace LogicLineages.OrdinalComparison.Source

noncomputable def successorRaw (n : Nat) : Nat :=
  actualCollapse (LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibration.block 1 (n + 2))

noncomputable def successorObservation (n : Nat) : Nat := successorRaw n - 1

end LogicLineages.OrdinalComparison.Source
