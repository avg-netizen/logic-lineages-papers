module
public import LogicLineages.PermittedControl.FiniteProfileDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual relative profile, not an interpretation defined by the code. -/
def RawProfileCorrect : Prop := ∀ mu e : NONote,
  rawProfileCode (rawNoteEncode mu.1) (rawNoteEncode e.1) = relativeProfile mu.1.repr e.1.repr

def RawProfileEffective : Prop := Primrec₂ rawProfileCode

/-- Every finite piece is constant for both actual profiles. -/
def JointProfilePieceConstant : Prop := ∀ mu nu x y : Ordinal.{0},
  mu < epsilonZero → nu < epsilonZero → SameProfilePiece mu nu x y →
  relativeProfile mu x = relativeProfile mu y ∧ relativeProfile nu x = relativeProfile nu y

/-- The literal finite list covers every exponent in the clipped domain,
including right endpoints and empty E<=2 cases, without a supplied cover. -/
def JointProfileFiniteCover : Prop := ∀ mu nu E x : Ordinal.{0},
  mu < epsilonZero → nu < epsilonZero → E < epsilonZero →
  2 ≤ x → x < E → ∃ y ∈ jointProfileRepresentatives mu nu E,
    SameProfilePiece mu nu x y

def FiniteProfileFoundation : Prop := RawProfileCorrect ∧ RawProfileEffective ∧
  JointProfilePieceConstant ∧ JointProfileFiniteCover

end LogicLineages.PermittedControl.Targets
