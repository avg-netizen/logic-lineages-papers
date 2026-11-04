module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowTargets

/-- Complete shared-valuation structural substitution, including arbitrary
Boolean matrices and every actual auxiliary arithmetic term. -/
def ExactSubstitution : Prop :=
  (∀ (a replacement : Term) (i : Nat) (ν : Nat → Nat),
    (a.substitute i replacement).value ν = a.value (Function.update ν i (replacement.value ν))) ∧
  (∀ (p : Matrix) (replacement : Term) (i : Nat) (ν : Nat → Nat),
    (p.substitute i replacement).eval ν ↔ p.eval (Function.update ν i (replacement.value ν)))

/-- Actual coefficient-close Phi arguments admit a finite displacement. This
depends on the proved exact Phi inverse supplier, with no growth/solver premise. -/
def ActualArgumentWindow : Prop :=
  ∀ a b c : Nat, Phi b ≤ Phi a → Phi a ≤ c * Phi b →
    ∃ d : Nat, d ≤ c ∧ a = b + d

/-- A genuine two/multi-variable existential elimination clause. The arbitrary
matrix p retains ALL other variables under one shared valuation. The only
independence is syntactic absence of the eliminated original name from anchor.
Signed source arguments and every finite exception are guarded literally. -/
def ActualFiniteElimination : Prop :=
  ∀ (i : Nat) (anchor : Term) (e : Int) (c : Nat) (p : Matrix),
    i ∉ anchor.variables → ∀ ν : Nat → Nat,
      (∃ n : Nat, (closeMatrix i anchor e c).eval (Function.update ν i n) ∧
        p.eval (Function.update ν i n)) ↔ (finiteWindow i anchor e c p).eval ν

/-- Elimination introduces no variable names and actually removes i when the
anchor omits i. These are membership claims, so duplicate occurrences remain
valid input rather than an assumed independent-coordinate representation. -/
def ExactWindowSupport : Prop :=
  ∀ (i : Nat) (anchor : Term) (e : Int) (c : Nat) (p : Matrix),
    i ∉ anchor.variables → ∀ j : Nat,
      j ∈ (finiteWindow i anchor e c p).variables →
        j ≠ i ∧ (j ∈ anchor.variables ∨ j ∈ p.variables)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowTargets
