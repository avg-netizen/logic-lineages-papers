module
public import LogicLineages.PermittedControl.ProfileBandReturnTargets
public import LogicLineages.PermittedControl.SensitiveUnitTargets

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual P=0 leading-phase step: the new cost is at beta, never the old
whole-state exponent beta+1. Every budget and large coefficient is derived. -/
def ActualPureSuccessorStep : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu beta A : Ordinal.{0}) (R t : Nat),
  mu < epsilonZero → beta < epsilonZero → A < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → 2 ≤ beta → 20 ≤ R →
  actualOrdinalNorm mu ≤ R → actualOrdinalNorm beta ≤ R →
  thickBlockTail R B ≤ t →
  actualLimitPart A=mu+Ordinal.omega0^(beta+1) → actualOrdinalNorm A=t →
  let X := f t-relativeProfile mu beta
  let v := 1+actualOrdinalNorm beta
  let q := X/v
  let r := actualMaximumPredecessor (Ordinal.omega0^beta) (X%v)
  descentWith f A-mu=Ordinal.omega0^beta*(q : Ordinal)+r ∧
  actualOrdinalNorm (descentWith f A)=f t ∧ R+2<q ∧ r<Ordinal.omega0^beta ∧
  Ordinal.log Ordinal.omega0 (descentWith f A-mu)=beta ∧
  actualLimitPart (descentWith f A-mu)=Ordinal.omega0^beta*(q : Ordinal)+actualLimitPart r

/-- Full actual successor entry-to-thick-or-divergence bridge. The common
large block, if needed, is derived from the actual next states. -/
def ActualPureSuccessorSeparation : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu beta A A' : Ordinal.{0}) (R t : Nat),
  mu < epsilonZero → nu < epsilonZero → beta < epsilonZero →
  A < epsilonZero → A' < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → (nu=0 ∨ Order.IsSuccLimit nu) →
  2 ≤ beta → 20 ≤ R → actualOrdinalNorm mu ≤ R → actualOrdinalNorm nu ≤ R →
  actualOrdinalNorm beta ≤ R → thickBlockTail R B ≤ t →
  actualLimitPart A=mu+Ordinal.omega0^(beta+1) →
  actualLimitPart A'=nu+Ordinal.omega0^(beta+1) →
  actualOrdinalNorm A=t → actualOrdinalNorm A'=t → relativeProfile mu beta<relativeProfile nu beta →
  OrientedUnitDivergence f mu nu (Ordinal.omega0^beta) A A'

def PureSuccessorFoundation : Prop := ActualPureSuccessorStep ∧ ActualPureSuccessorSeparation

end LogicLineages.PermittedControl.Targets
