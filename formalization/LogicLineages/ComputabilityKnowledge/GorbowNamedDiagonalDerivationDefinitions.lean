module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentence

@[expose] public section
/-! Literal diagonal syntax reused without the old diagram theory. Calibration
below is explicitly supplied by paid concrete PR witnesses. Numeral instances
are not universally quantified internal closure laws or source Base adequacy. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation
open GorbowPRProgram GorbowSourceRegistryPadding List.Vector

def Calibrated (pF pR : Program 1) : Prop :=
  (∀ code, evaluate pF (code ::ᵥ List.Vector.nil) = sourceFunction code) ∧
  (∀ code, evaluate pR (code ::ᵥ List.Vector.nil) = sourceRelationValue code)

end LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation
