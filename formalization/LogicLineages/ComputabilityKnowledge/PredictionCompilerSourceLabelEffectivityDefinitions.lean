module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodecProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelEffectivity
open Turing.PartrecToTM2 PredictionCompilerFinitePayloadCodec PredictionCompilerSourceLabelExplicitCodec

/-- Literal one-layer destructor with canonical dummy children. -/
def inspect : Label → Nat × Nat × Quint Label
  | .move p k₁ k₂ q => (0, putNat (p,k₁,k₂), q,.ret .halt,.ret .halt,.ret .halt,.ret .halt)
  | .clear p k q => (1, putNat (p,k), q,.ret .halt,.ret .halt,.ret .halt,.ret .halt)
  | .copy q => (2, 0, q,.ret .halt,.ret .halt,.ret .halt,.ret .halt)
  | .push k s q => (3, putNat (k,s), q,.ret .halt,.ret .halt,.ret .halt,.ret .halt)
  | .read f => (4, 0, f none, f (some .consₗ), f (some .cons), f (some .bit0), f (some .bit1))
  | .succ q => (5, 0, q,.ret .halt,.ret .halt,.ret .halt,.ret .halt)
  | .pred q₁ q₂ => (6, 0, q₁,q₂,.ret .halt,.ret .halt,.ret .halt)
  | .ret k => (7, putNat k, .ret .halt,.ret .halt,.ret .halt,.ret .halt,.ret .halt)
end LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelEffectivity
