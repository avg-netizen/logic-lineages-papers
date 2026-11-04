module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseDefinitions
public import Mathlib.Computability.Primrec.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverse.Targets

/-- Actual Phi and ACTUAL fixed-seed H graphs on ALL natural inputs, including
inputs below Phi(0)/H(0). No monotonicity or unproved inverse premise supplied. -/
def ExactOriginalGraphs : Prop :=
  FloorGraph Phi phiInverse ∧
  FloorGraph FixedSeedControlResidue.H hyperInverse

/-- Round trips, total zero convention, monotonicity, actual search bound and
both threshold eliminations; every integer quantified here is natural. -/
def OriginalOrderAndRoundTrips : Prop :=
  (∀ n : Nat, phiInverse (Phi n) = n ∧
    hyperInverse (FixedSeedControlResidue.H n) = n) ∧
  phiInverse 0 = 0 ∧ hyperInverse 0 = 0 ∧
  Monotone phiInverse ∧ Monotone hyperInverse ∧
  (∀ x : Nat, phiInverse x ≤ x ∧ hyperInverse x ≤ x) ∧
  (∀ x n : Nat, 0 < n →
    (phiInverse x < n ↔ x < Phi n) ∧
    (n ≤ phiInverse x ↔ Phi n ≤ x) ∧
    (hyperInverse x < n ↔ x < FixedSeedControlResidue.H n) ∧
    (n ≤ hyperInverse x ↔ FixedSeedControlResidue.H n ≤ x))

/-- Source Lemma3's effective coefficient-compression inequality with the
explicit total bound d(a)=a, for BOTH actual controls and EVERY x,a including0.
This pays a concrete elimination supplier, not quantifier elimination itself. -/
def EffectiveCoefficientCompression : Prop :=
  ∀ a x : Nat,
    phiInverse (a * x) ≤ phiInverse x + coefficientShift a ∧
    hyperInverse (a * x) ≤ hyperInverse x + coefficientShift a

/-- Genuine primitive recursion of the exact bounded numerical searches under
standard Nat coding, with no solver/evaluator/effectivity oracle. -/
def ActualPrimitiveRecursion : Prop :=
  Primrec phiInverse ∧ Primrec hyperInverse ∧ Primrec coefficientShift

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverse.Targets
