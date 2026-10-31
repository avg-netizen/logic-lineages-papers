module
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearch
/-- Radius-indexed tests; the caller must supply the actual finite coordinate box. -/
def Good (bad : Nat → Nat → Bool) (q : Nat) : Prop := ∀ r, bad q r = false
/-- A total computable radius bound for false queries. -/
def HasComputableBound (bad : Nat → Nat → Bool) : Prop :=
  ∃ b : Nat → Nat, Computable b ∧ ∀ q, ¬ Good bad q →
    ∃ r ≤ b q, bad q r = true
/-- Inclusive finite prefix: radius zero is tested, including zero-coordinate boxes. -/
def prefixBad (bad : Nat → Nat → Bool) (q : Nat) : Nat → Bool
  | 0 => bad q 0
  | n + 1 => prefixBad bad q n || bad q (n + 1)
end LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearch
