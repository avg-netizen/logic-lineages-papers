module

public import LogicLineages.ComputabilityKnowledge.PolynomialComparison
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Independent actual computability target for both composed output maps,
with faithful bound/term output codec and exact orientation correspondence.
The input domain is the explicit integer-monomial Code, not an unencoded
MvPolynomial quotient and not an assumed MRDP reduction. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.PolynomialComparisonEffectivity

open PolynomialCircuit
open LogicLineages.ComputabilityKnowledge.PolynomialComparison

def OutputCodecFaithful : Prop := Function.Injective CircuitComparison.encodeComparison

def StrictCorrespondence : Prop :=
  ∀ p : Code, strictCode (PolynomialCircuit.encode p) =
    some (CircuitComparison.encodeComparison (strictOutput p))

def WeakCorrespondence : Prop :=
  ∀ p : Code, weakCode (PolynomialCircuit.encode p) =
    some (CircuitComparison.encodeComparison (weakOutput p))

def Target : Prop := OutputCodecFaithful ∧ StrictCorrespondence ∧ WeakCorrespondence ∧
  Computable strictCode ∧ Computable weakCode

end LogicLineages.ComputabilityKnowledge.Comparators.PolynomialComparisonEffectivity
