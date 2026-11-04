module
public import LogicLineages.OrdinalComparison.FixedSeedControlResidueDefinitions
public import Mathlib.Data.Nat.Find
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverse

/-- Literal bounded greatest-index search. The bound is the actual input,
not an oracle. For the actual source controls g(n)>n, it searches every possible
preimage. If the input is below g(0), return0 as in Snyatkov p40. -/
def floorInverse (g : Nat → Nat) (x : Nat) : Nat :=
  Nat.findGreatest (fun n => g n ≤ x) x

def phiInverse : Nat → Nat := floorInverse Phi
def hyperInverse : Nat → Nat := floorInverse FixedSeedControlResidue.H

/-- The exact totalized inverse graph in the extended arithmetic signature.
At index0 the lower inequality is intentionally absent; below the first range
point the inverse is0. No inverse function is introduced into the RHS. -/
def FloorGraph (g inverse : Nat → Nat) : Prop :=
  ∀ x n : Nat, inverse x = n ↔
    (n = 0 ∨ g n ≤ x) ∧ x < g (n + 1)

/-- Effective coefficient bound for the actual source controls. -/
def coefficientShift (a : Nat) : Nat := a

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverse
