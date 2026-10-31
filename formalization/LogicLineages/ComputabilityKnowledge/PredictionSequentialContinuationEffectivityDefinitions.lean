module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodecProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivity
open PredictionSequentialContinuationCodec

def cases {α : Type} (z : α) (step : Frame → Cont → α) : Cont → α
  | .halt => z
  | .cons₁ c k => step (some (.inl c)) k
  | .cons₂ k => step none k
  | .comp c k => step (some (.inr (.inl c))) k
  | .fix c k => step (some (.inr (.inr c))) k
end LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivity
