module

public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShift
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Actual encoded domain-conversion certificate. Input/output use the same
faithful explicit coefficient-and-variable-list codec; no extraction algorithm
from an abstract MvPolynomial value is presumed. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.PolynomialDomainShiftEffectivity

open PolynomialCircuit
open LogicLineages.ComputabilityKnowledge.PolynomialDomainShift

def InputCodecFaithful : Prop := ∀ p : Code, PolynomialCircuit.decode (PolynomialCircuit.encode p) = some p

def OutputCodecFaithful : Prop := Function.Injective PolynomialCircuit.encode

def CodeCorrespondence : Prop :=
  ∀ p : Code, encodedShift (PolynomialCircuit.encode p) = some (PolynomialCircuit.encode (shift p))

def Target : Prop := InputCodecFaithful ∧ OutputCodecFaithful ∧ CodeCorrespondence ∧ Computable encodedShift

end LogicLineages.ComputabilityKnowledge.Comparators.PolynomialDomainShiftEffectivity
