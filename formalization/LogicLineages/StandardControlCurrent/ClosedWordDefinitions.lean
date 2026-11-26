module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.ClosedWord
open OrdinalComparison WordLinearDecisionCompletion

abbrev Bounds := List (Nat × Nat)

def BoundsHold (bs : Bounds) (ν : Nat → Nat) : Prop :=
  ∀ b ∈ bs, b.2 ≤ ν b.1

def boundAtom (b : Nat × Nat) : Atom :=
  .nonnegative (-(b.2 : Int), [(1, (b.1, []))])

def withBounds (bs : Bounds) (p : Formula) : Formula :=
  bs.foldr (fun b q => .conj (.atom (boundAtom b)) q) p

def withBoundsCode (bs : Bounds) (code : Nat) : Nat :=
  bs.foldr (fun b q => 6 * Nat.pair (6 * Encodable.encode (boundAtom b).data + 2) q + 4) code

noncomputable def solve (D : Nat) (bs : Bounds) (code : Nat) : Bool :=
  ClosedWordDecisionCompletion.Machine.solve D (withBoundsCode bs code)

/-- This checks the literal occurrence-domain proposition, not atom truth. -/
def Adequate (bs : Bounds) (p : Formula) : Prop :=
  ∀ ν, BoundsHold bs ν → Formula.meaningful p ν
end LogicLineages.StandardControlCurrent.ClosedWord
