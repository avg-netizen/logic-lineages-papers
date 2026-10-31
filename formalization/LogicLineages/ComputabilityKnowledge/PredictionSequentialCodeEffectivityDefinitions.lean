module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodecProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeEffectivity
open PredictionSequentialCodeCodec
/-- One-layer case analysis on the actual sequential program constructors.
The unused second fix argument is the genuine zero program. -/
def cases {α : Type} (leaf : Nat → α) (branch : Nat → Code → Code → α) : Code → α
  | .zero' => leaf 0
  | .succ => leaf 1
  | .tail => leaf 2
  | .cons a b => branch 3 a b
  | .comp a b => branch 4 a b
  | .case a b => branch 5 a b
  | .fix a => branch 6 a .zero'
end LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeEffectivity
