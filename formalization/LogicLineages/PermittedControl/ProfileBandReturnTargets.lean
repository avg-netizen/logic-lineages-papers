module
public import LogicLineages.PermittedControl.InitialPeelingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Genuine pointwise-profile coupling from an actual pure leading limit to
an affordable lower pure target. Costs at E and starting finite tails need
not agree. The E=zeta boundary is a real zero-step first hit. -/
def ActualProfileBandReturn : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu E zeta A A' : Ordinal.{0}) (R t : Nat),
  mu < epsilonZero → nu < epsilonZero → E < epsilonZero → zeta < epsilonZero →
  A < epsilonZero → A' < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → (nu=0 ∨ Order.IsSuccLimit nu) →
  1 ≤ zeta → zeta ≤ E → 20 ≤ R →
  actualOrdinalNorm mu ≤ R → actualOrdinalNorm nu ≤ R →
  actualOrdinalNorm E ≤ R → actualOrdinalNorm zeta ≤ R →
  thickBlockTail R B ≤ t →
  actualLimitPart A=mu+Ordinal.omega0^E →
  actualLimitPart A'=nu+Ordinal.omega0^E →
  actualOrdinalNorm A=t → actualOrdinalNorm A'=t →
  (∀ e : Ordinal.{0}, zeta ≤ e → e < E → relativeProfile mu e=relativeProfile nu e) →
  ∃ i : Nat, FirstEntry f A (mu+Ordinal.omega0^zeta) i ∧
    FirstEntry f A' (nu+Ordinal.omega0^zeta) i ∧
    actualOrdinalNorm ((descentWith f)^[i] A)=f^[i] t ∧
    actualOrdinalNorm ((descentWith f)^[i] A')=f^[i] t

end LogicLineages.PermittedControl.Targets
