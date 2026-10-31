module
public import Mathlib.Computability.Partrec
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalBounds

/-- Zero-based `g i` represents source entry `g_(i+1)`. Each prefix includes
all input arguments from zero through n. -/
def inputMax (g : Nat → Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => g i 0
  | n+1 => max (inputMax g i n) (g i (n+1))

/-- The source f_m uses the first m entries, `i < m`. The extra level f_0=0
is only an auxiliary convention, not an extra source listing entry. -/
def levelBound (g : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | m+1, n => max (levelBound g m n) (inputMax g m n)

def diagonal (g : Nat → Nat → Nat) (n : Nat) : Nat := levelBound g (n+1) n

/-- Literal coverage hypothesis. Uniform computability and primitive
recursiveness of each fixed entry are separate hypotheses; uniform primitive
recursiveness of a complete evaluator is never assumed. -/
def CoversPR (g : Nat → Nat → Nat) : Prop :=
  ∀ f : Nat → Nat, Primrec f → ∃ i, ∀ n, g i n = f n
end LogicLineages.ComputabilityKnowledge.PredictionOriginalBounds
