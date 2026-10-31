module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodecProof
public import Mathlib.Computability.TuringMachine.ToPartrec
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodec
open PredictionSequentialCodeCodec
abbrev Cont := Turing.PartrecToTM2.Cont'
abbrev Frame := Option (Code ⊕ (Code ⊕ Code))

def toList : Cont → List Frame
  | .halt => []
  | .cons₁ c k => some (.inl c) :: toList k
  | .cons₂ k => none :: toList k
  | .comp c k => some (.inr (.inl c)) :: toList k
  | .fix c k => some (.inr (.inr c)) :: toList k

def push : Frame → Cont → Cont
  | none, k => .cons₂ k
  | some (.inl c), k => .cons₁ c k
  | some (.inr (.inl c)), k => .comp c k
  | some (.inr (.inr c)), k => .fix c k

def fromList (xs : List Frame) : Cont := xs.foldr push .halt

def code (k : Cont) : Nat := Encodable.encode (toList k)

/-- Total decoding; malformed list words are interpreted as the empty continuation. -/
def decode (n : Nat) : Cont := fromList ((Encodable.decode (α := List Frame) n).getD [])

def fold {α : Type} (z : α) (step : Frame → α → α) : Cont → α
  | .halt => z
  | .cons₁ c k => step (some (.inl c)) (fold z step k)
  | .cons₂ k => step none (fold z step k)
  | .comp c k => step (some (.inr (.inl c))) (fold z step k)
  | .fix c k => step (some (.inr (.inr c))) (fold z step k)
end LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodec
