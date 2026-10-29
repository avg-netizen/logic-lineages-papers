module

public import LogicLineages.ComputabilityKnowledge.CircuitReduction
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Separately pending computational certificate for the explicit circuit codec.
A semantic CircuitReduction proof alone does not prove this target. In particular
an executable definition or Encodable instance is not its Computable certificate. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.CircuitReductionEffectivity

open LogicLineages.ComputabilityKnowledge.CircuitReduction

def InputCodecFaithful : Prop :=
  ∀ c : Circuit, decodeCircuit (encodeCircuit c) = some c

def OutputCodecFaithful : Prop := Function.Injective encodeSystem

def CodeCorrespondence : Prop :=
  ∀ c : Circuit, compileCode (encodeCircuit c) = some (encodeSystem (compile c))

/-- Computable is Mathlib's partial-recursive-code definition on Primcodable data. -/
def Target : Prop := InputCodecFaithful ∧ OutputCodecFaithful ∧
  CodeCorrespondence ∧ Computable compileCode

end LogicLineages.ComputabilityKnowledge.Comparators.CircuitReductionEffectivity
