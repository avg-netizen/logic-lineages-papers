module

public import LogicLineages.ComputabilityKnowledge.CircuitComparison
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Separate actual recursive-function certificates for BOTH output orientations:
strict(V,U) and weak(V+1,U), including the explicit finite-variable-bound header.
Faithfulness is required on all encoded bound/term pairs, not only compiler outputs.
No merely executable reconstruction substitutes for weakCode computability. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.CircuitComparisonEffectivity

open CircuitReduction
open LogicLineages.ComputabilityKnowledge.CircuitComparison

def OutputCodecFaithful : Prop := Function.Injective encodeComparison

def StrictCorrespondence : Prop :=
  ∀ c : Circuit, strictCode (encodeCircuit c) = some (encodeComparison (strictOutput c))

def WeakCorrespondence : Prop :=
  ∀ c : Circuit, weakCode (encodeCircuit c) = some (encodeComparison (weakOutput c))

def Target : Prop := OutputCodecFaithful ∧ StrictCorrespondence ∧ WeakCorrespondence ∧
  Computable strictCode ∧ Computable weakCode

end LogicLineages.ComputabilityKnowledge.Comparators.CircuitComparisonEffectivity
