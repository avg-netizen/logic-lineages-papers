module
public import LogicLineages.OrdinalComparison.ProfileDominatorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:direct (499–519), executable principal choice and threshold.
Only finite normal syntax is computed; actual ordinal semantics are calibrated. -/
def ActualProfileLeadingNoteCalibration : Prop :=
  ∀ rho : NONote, (profileLeadingNote rho).1.repr = actualProfileLeadingMonomial rho ∧
    Vendor.R1.treeWeight (profileLeadingNote rho).1 = profileLeadingWeight rho

def ActualProfilePrincipalDominator : Prop :=
  ∀ L : Ordinal.{0}, Ordinal.omega0 < L → ∀ word : List NONote,
    (∀ rho ∈ word, Order.IsSuccLimit rho.1.repr ∧ rho.1.repr < L) →
    let pi := (profilePrincipalDominator word).1.repr
    Ordinal.omega0 ≤ pi ∧ pi < L ∧ pi < epsilonZero ∧
    (∀ rho ∈ word, actualProfileLeadingMonomial rho ≤ pi) ∧
    ∃ beta : Ordinal.{0}, 0 < beta ∧ pi = Ordinal.omega0 ^ beta

def ActualProfileDirectThresholdCalibration : Prop :=
  ∀ L : NONote, ∀ E : FixedLimitPositiveExpr,
    profileDirectThreshold L E = max (fixedLimitProfileThreshold E)
      (max (profileReserveBlocks (profileBoundWord E) *
        actualOrdinalNorm (profilePrincipalDominator (profileBoundWord E)).1.repr)
        (max 4 (actualOrdinalNorm L.1.repr)))

end LogicLineages.OrdinalComparison.Targets
