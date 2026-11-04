module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollisionDefinitions
public import Mathlib.Computability.Primrec.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollision.Targets

/-- Actual inverse-based coefficient elimination, on ALL natural a,b,c.
No eventual-growth, inverse-correctness or solver assumption is supplied. -/
def ActualCoefficientElimination : Prop := ∀ a b c : Nat,
  Phi a ≤ c * Phi b → a ≤ b + c

/-- Actual source Lemma4, strengthened to nonstrict comparison, with an
explicit finite window for the SMALLER hyper-index. Also pays exact signed
arguments above that bound. No unsupported bound on the larger index. -/
def FiniteWindowAndDomains : Prop :=
  (∀ (c : Nat) (e k : Int) (u v : Nat),
    v < u → translatedValue u e ≤ c * translatedValue v k →
    v < collisionBound c e k) ∧
  (∀ (c : Nat) (e k : Int) (u v : Nat),
    collisionBound c e k ≤ v → v ≤ u →
    0 ≤ (FixedSeedControlResidue.H u : Int) + e ∧
    0 ≤ (FixedSeedControlResidue.H v : Int) + k ∧
    (shiftedInput u e : Int) = (FixedSeedControlResidue.H u : Int) + e ∧
    (shiftedInput v k : Int) = (FixedSeedControlResidue.H v : Int) + k)

/-- Literal programs for signed arguments, source terms and the concrete
window; these are uniform in EVERY original signed shift/coefficient code. -/
def ActualPrimitiveRecursion : Prop :=
  Primrec₂ shiftedInput ∧ Primrec₂ translatedValue ∧ Primrec boundCode

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollision.Targets
