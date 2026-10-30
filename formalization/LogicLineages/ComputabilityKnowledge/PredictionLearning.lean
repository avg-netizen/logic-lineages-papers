module

public import LogicLineages.ComputabilityKnowledge.PredictionGame
public import Mathlib.Computability.PartrecCode

@[expose] public section

/-! Ordinary partial-recursive programs on actual finite binary histories,
and bounded certificates for an error in the source simultaneous prediction
game. Bounded failure is NOT a divergent or incorrect actual play. No runtime
model or hierarchy theorem is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionLearning

open PredictionGame
abbrev Code := Nat.Partrec.Code

def bitValue (b : Bool) : Nat := if b then 1 else 0

def decodeBit (n : Nat) : Option Bool :=
  if n = 0 then some false else if n = 1 then some true else none

/-- The actual partial program halts with a binary value on every finite
binary history. This is a promise, not a computable totality test. -/
def TotalBinary (p : Code) : Prop :=
  ∀ h : List Bool, ∃ b : Bool,
    bitValue b ∈ Nat.Partrec.Code.eval p (Encodable.encode h)

noncomputable def policy (p : Code) (hp : TotalBinary p) : Policy :=
  fun h => Classical.choose (hp h)

def boundedMove (p : Code) (fuel : Nat) (h : List Bool) : Option Bool :=
  (Nat.Partrec.Code.evaln fuel p (Encodable.encode h)).bind decodeBit

/-- First component: past evasions; second: past predictions. Both current
moves use the OLD histories, exactly as in PredictionGame.advance. -/
def boundedPlay (p e : Code) (fuel : Nat) : Nat → Option (List Bool × List Bool)
  | 0 => some ([], [])
  | n + 1 => do
      let h ← boundedPlay p e fuel n
      let a ← boundedMove p fuel h.1
      let b ← boundedMove e fuel h.2
      pure (h.1 ++ [b], h.2 ++ [a])

def boundedError (p e : Code) (fuel n : Nat) : Option Bool := do
  let h ← boundedPlay p e fuel n
  let a ← boundedMove p fuel h.1
  let b ← boundedMove e fuel h.2
  pure (a != b)

/-- The universal index encodes an error round and a common finite stage.
Reject only a valid post-cutoff error certificate. -/
def learningMatrix (p e : Code) (cutoff certificate : Nat) : Bool :=
  if cutoff ≤ certificate.unpair.1 then
    !((boundedError p e certificate.unpair.2 certificate.unpair.1).getD false)
  else true

end LogicLineages.ComputabilityKnowledge.PredictionLearning
