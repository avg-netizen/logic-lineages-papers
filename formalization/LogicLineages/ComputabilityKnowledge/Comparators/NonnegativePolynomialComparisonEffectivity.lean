module

public import LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparison
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Both actual composed code maps, with exact (V,U)/(V+1,U) orientations.
The semantic reduction is on well-formed explicit polynomial codes. No
computable extraction from an abstract polynomial or MRDP supplier is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.NonnegativePolynomialComparisonEffectivity

open PolynomialCircuit
open LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparison

def OutputCodecFaithful : Prop := Function.Injective CircuitComparison.encodeComparison

def StrictCorrespondence : Prop :=
  ∀ p : Code, strictCode (PolynomialCircuit.encode p) =
    some (CircuitComparison.encodeComparison (strictOutput p))

def WeakCorrespondence : Prop :=
  ∀ p : Code, weakCode (PolynomialCircuit.encode p) =
    some (CircuitComparison.encodeComparison (weakOutput p))

def Target : Prop := OutputCodecFaithful ∧ StrictCorrespondence ∧ WeakCorrespondence ∧
  Computable strictCode ∧ Computable weakCode

end LogicLineages.ComputabilityKnowledge.Comparators.NonnegativePolynomialComparisonEffectivity
