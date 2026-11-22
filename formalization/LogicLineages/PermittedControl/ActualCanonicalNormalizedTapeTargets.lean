module
public import LogicLineages.PermittedControl.ActualNormalizedTapeTargets
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalNormalizedTape
open ActualZeroClassReplacement ActualNormalizedTape ActualCanonicalOperandGrouping

/-- At the same actual f and valuation, transport the complete source
and output read certificate to the literal first-occurrence tape. -/
def ExactCanonicalTapeCertificate : Prop :=
  ∀ (f ρ : Nat → Nat) (raw xs : List Read),
    liftedReads f ρ raw → normalizeCanonical f ρ raw = some xs →
    NormalizedTape f ρ raw xs

/-- Existence is exactly payment of every true source occurrence,
before discarding any zero or canceled key. -/
def ExactCanonicalTapeDomain : Prop :=
  ∀ (f ρ : Nat → Nat) (raw : List Read),
    liftedReads f ρ raw ↔ ∃ xs, normalizeCanonical f ρ raw = some xs ∧
      NormalizedTape f ρ raw xs

def FullActualCanonicalNormalizedTape : Prop :=
  ExactCanonicalTapeCertificate ∧ ExactCanonicalTapeDomain

end LogicLineages.PermittedControl.ActualCanonicalNormalizedTape
