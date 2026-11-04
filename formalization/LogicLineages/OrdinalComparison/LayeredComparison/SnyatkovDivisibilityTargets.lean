module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibilityDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibility.Targets

/-- Source p43 elimination of modular tests on actual f/H/f(H+e) terms.
ANY signed affine coefficient/outer constant and ALL original natural inputs,
including every finite exception. Positive modulus is the source domain. -/
def ExactFiniteTailElimination : Prop := ∀ p : Parameters, 0 < p.2.1 →
  (∀ n : Nat, cutoff p ≤ n → predicate p n = tailBit p) ∧
  (∀ n : Nat, predicate p n = true ↔
    (n < cutoff p ∧ (smallBits p).getD n false = true) ∨
    (cutoff p ≤ n ∧ tailBit p = true))

/-- Actual literal BASE formula truth at EVERY raw valuation with exact ONE
original variable-set membership. H/modulus/inverse are absent from output
syntax; source atoms and actual data are not treated as uninterpreted symbols. -/
def LiteralBaseTruthAndSupport : Prop := ∀ i : Nat, ∀ p : Parameters,
  0 < p.2.1 →
  (∀ ν : Nat → Nat, (sourceFormula i p).eval ν ↔ predicate p (ν i) = true) ∧
  (∀ j : Nat, j ∈ (sourceFormula i p).variables ↔ j = i)

/-- All-code literal postfix calibration, including zero modulus and arbitrary
tag/signed input codes. No semantic validity is claimed for zero modulus. -/
def ExactCodeCalibration : Prop := ∀ i : Nat, ∀ p : Parameters,
  formulaCode i p = (sourceFormula i p).encode

/-- Actual uniform primitive recursion of the explicit finite normal form
and literal BASE code, with every signed input/coefficient retained. -/
def ActualPrimitiveRecursion : Prop :=
  Primrec cutoff ∧ Primrec₂ predicate ∧ Primrec tailBit ∧ Primrec smallBits ∧
  Primrec₂ formulaCode

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibility.Targets
