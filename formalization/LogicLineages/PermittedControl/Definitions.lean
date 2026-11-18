module
public import LogicLineages.OrdinalComparison.ControlDefinitions
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl

/-- Paper 17's literal F5(n+100), shared only because its definition agrees. -/
abbrev G := OrdinalComparison.Phi

/-- Least common multiple of 1,...,n, with empty value 1. -/
def initialLcm : Nat → Nat
  | 0 => 1
  | n + 1 => Nat.lcm (initialLcm n) (n + 1)

/-- The paper's p(n)=floor(n/2). -/
def potential (n : Nat) : Nat := n / 2

/-- The remainder is computed in integers: the printed numerator can be negative. -/
def correction (n : Nat) : Nat :=
  ((2 * (potential n : Int) - 2 - (G n : Int)) % (2 * (initialLcm n : Int))).toNat

/-- Exact near-standard control, retaining the whole prescribed prefix [0,b]. -/
def nearControl (b n : Nat) : Nat :=
  if n ≤ b then G n else G n + correction n

end LogicLineages.PermittedControl
