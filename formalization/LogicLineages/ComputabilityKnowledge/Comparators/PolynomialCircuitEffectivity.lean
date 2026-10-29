module

public import LogicLineages.ComputabilityKnowledge.PolynomialCircuit
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Separate explicit-code effectivity contract. Sign/magnitude and length frames
must faithfully encode the entire monomial list. Computable is the actual
Mathlib partial-recursive-code notion, not an executability assertion. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.PolynomialCircuitEffectivity

open LogicLineages.ComputabilityKnowledge.PolynomialCircuit

def InputCodecFaithful : Prop := ∀ p : Code, decode (encode p) = some p

def CodeCorrespondence : Prop :=
  ∀ p : Code, compileCode (encode p) = some (CircuitReduction.encodeCircuit (compile p))

def Target : Prop := InputCodecFaithful ∧ CodeCorrespondence ∧ Computable compileCode

end LogicLineages.ComputabilityKnowledge.Comparators.PolynomialCircuitEffectivity
