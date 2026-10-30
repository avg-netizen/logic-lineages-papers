module

public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

@[expose] public section

/-! Literal original ordinal argument of H=ψ(ω·R+g), with natural product
and sum, including zero edgecases for the numeric calibration supplier. -/
namespace LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibration

open LogicLineages.OrdinalComparison

noncomputable def block (n g : Nat) : Ordinal.{0} :=
  ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 (n : Ordinal)) (g : Ordinal)

end LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibration
