module
public import LogicLineages.PermittedControl.PureSuccessorTargets

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual event-one separation in an admitted top-clipped constant-profile
band. The fixed witness and all source norm bounds are explicit; no next
maximum, saturation, visit, or equal-finite-tail premise is supplied. -/
def ActualPureLimitSeparation : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu E zeta A A' : Ordinal.{0}) (R t : Nat),
  mu < epsilonZero → nu < epsilonZero → E < epsilonZero → zeta < epsilonZero →
  A < epsilonZero → A' < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → (nu=0 ∨ Order.IsSuccLimit nu) →
  Order.IsSuccLimit E → 2 ≤ zeta → zeta < E → 20 ≤ R →
  actualOrdinalNorm mu ≤ R → actualOrdinalNorm nu ≤ R →
  actualOrdinalNorm E ≤ R → actualOrdinalNorm zeta ≤ R → thickBlockTail R B ≤ t →
  actualLimitPart A=mu+Ordinal.omega0^E → actualLimitPart A'=nu+Ordinal.omega0^E →
  actualOrdinalNorm A=t → actualOrdinalNorm A'=t →
  (∀ e : Ordinal.{0}, zeta ≤ e → e < E → relativeProfile mu e=relativeProfile mu zeta) →
  (∀ e : Ordinal.{0}, zeta ≤ e → e < E → relativeProfile nu e=relativeProfile nu zeta) →
  relativeProfile mu zeta<relativeProfile nu zeta →
  actualLimitPart (descentWith f A'-nu) < actualLimitPart (descentWith f A-mu) ∧
  Ordinal.omega0^zeta ≤ actualLimitPart (descentWith f A-mu) ∧
  Ordinal.omega0^zeta ≤ actualLimitPart (descentWith f A'-nu) ∧
  actualOrdinalNorm (descentWith f A)=f t ∧ actualOrdinalNorm (descentWith f A')=f t

end LogicLineages.PermittedControl.Targets
