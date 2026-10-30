module
public import LogicLineages.OrdinalComparison.LimitMassFirstDefinitions
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 strict-mass theorem702–717: exact identity-profile compiler data
and limit-exponent base threshold. Full successor induction remains separate. -/
def ActualIdentityProfileCalibration : Prop :=
  profileBoundWord .input = [profileOmegaNote] ∧
  profileReserveBlocks (profileBoundWord .input) = 3 ∧
  profileReserveLeadingBound (profileBoundWord .input) = 2 ∧
  fixedLimitProfileThreshold .input = 4 ∧
  ∀ L : NONote, profileLimitMassThreshold L .input = max 7 (actualOrdinalNorm L.1.repr+1)

def ActualLimitKernelStrictMass : Prop :=
  ∀ L : NONote, ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta →
    L.1.repr = Ordinal.omega0^beta → ∀ t c e : Nat,
    max 7 (actualOrdinalNorm L.1.repr+1) ≤ t → c < e →
    e+actualOrdinalNorm L.1.repr ≤ t →
      actualSuffixKernel L.1.repr e t < actualSuffixKernel L.1.repr c t

end LogicLineages.OrdinalComparison.Targets
