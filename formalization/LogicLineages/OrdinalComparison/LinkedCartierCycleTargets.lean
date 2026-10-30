module
public import LogicLineages.OrdinalComparison.BinaryCartierExtensionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Properness is established for the literal source numerator, not assumed
as an additional initial-state hypothesis. -/
def ActualLinkedCartierInitialProper : Prop :=
  ∀ u : Nat, 5 ≤ u →
    (Polynomial.X ^ (actualLinkedOffset u - 1) : Polynomial (ZMod 2)).degree <
      (actualBinarySourceDimension (actualLinkedCutoff u) : WithBot Nat)

/-- Complete-state eventual existence for the original source omega over the
actual algebraic closure. This does not identify a scalar bit's least period. -/
def ActualSourceCartierEventualCycle : Prop :=
  ∀ v : Nat, 4 ≤ v → ∃ j p : Nat, 0 < p ∧ ∀ k : Nat,
    (actualDifferentialCartier^[j + k + p]) (actualLinkedDifferential (Phi v)) =
      (actualDifferentialCartier^[j + k]) (actualLinkedDifferential (Phi v))

end LogicLineages.OrdinalComparison.Targets
