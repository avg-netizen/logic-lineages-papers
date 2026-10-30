module

public import LogicLineages.ComputabilityKnowledge.PredictionLearning

@[expose] public section

/-! Exact ordinary-program version of the anti-predictor used in paper14's
finite-values proof. The partial computation is independent of a totality
proof. It reconstructs the complement prefix and uses only input length.
Its partial recursiveness and uniform compiler are obligations, not fields.
No source input-tape runtime is identified with bounded evaln stages. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionAntiProgram

open PredictionLearning PredictionGame

def partialMove (p : Code) (h : List Bool) : Part Bool := do
  let n ← Nat.Partrec.Code.eval p (Encodable.encode h)
  Part.ofOption (decodeBit n)

def partialAntiPrefix (p : Code) : Nat → Part (List Bool)
  | 0 => pure []
  | n + 1 => do
      let h ← partialAntiPrefix p n
      let b ← partialMove p h
      pure (h ++ [!b])

def antiProgram (p : Code) (input : Nat) : Part Nat :=
  match Encodable.decode (α := List Bool) input with
  | none => pure 0
  | some h => do
      let xs ← partialAntiPrefix p h.length
      let b ← partialMove p xs
      pure (bitValue (!b))

/-- Ordinary s-m-n specialization of one fixed universal anti-program code.
The existence of a suitable universal code must be proved from the actual
partial computation above. This is not an assumed compiler supplier. -/
def compiledAnti (universal p : Code) : Code :=
  Nat.Partrec.Code.curry universal (Encodable.encode p)

end LogicLineages.ComputabilityKnowledge.PredictionAntiProgram
