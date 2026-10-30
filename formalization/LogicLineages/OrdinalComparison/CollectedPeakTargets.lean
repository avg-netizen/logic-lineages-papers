module
public import LogicLineages.OrdinalComparison.CollectedPeakDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedPositiveInputLower : Prop :=
  ∀ A : CollectedPositiveNF, CollectedPositiveValid A → collectedPositiveSupport A=true →
    ∀ x : Nat, x ≤ actualCollectedPositiveEval A x

def CollectedAtomNormDecomposition : Prop :=
  ∀ (rho : NONote) (c b : Nat) (tags : CollectedPositiveTags),
    Order.IsSuccLimit rho.1.repr → rho.1.repr<epsilonZero → ∀ x : Nat,
      actualOrdinalNorm (actualCollectedTagInput rho (.mk c b tags) x)=
        actualOrdinalNorm rho.1.repr + c + b*x + actualCollectedTagsEval tags x

def CollectedHeadPeakBand : Prop :=
  ∀ (rho : NONote) (A : CollectedPositiveNF),
    Order.IsSuccLimit rho.1.repr → rho.1.repr<epsilonZero →
    CollectedPositiveValid A → collectedPositiveSupport A=true → ∀ x : Nat, 2≤x →
      actualCollectedTagInput rho A x<epsilonZero ∧
      Ordinal.omega0≤actualCollectedTagInput rho A x ∧
      Phi x≤actualCollectedTagPeak rho A x ∧
      actualCollectedTagPeak rho A x<actualProfileHead rho (actualCollectedPositiveEval A x) ∧
      actualProfileHead rho (actualCollectedPositiveEval A x)<2*actualCollectedTagPeak rho A x ∧
      ∃ s : Nat, actualCollectedTagPeak rho A x=Phi s ∧
        2*actualCollectedTagPeak rho A x<Phi (s+1)

def CollectedMaximumPeak : Prop :=
  ∀ tags : CollectedPositiveTags, CollectedTagsValid tags → tags≠.nil → ∀ x : Nat, 2≤x →
    0<collectedCoefficientSum tags ∧ Phi x≤actualCollectedMaximumPeak tags x ∧
    (∃ (rho : NONote) (A : CollectedPositiveNF) (a : Nat),
      (rho,A,a)∈collectedTagEntries tags ∧
      actualCollectedMaximumPeak tags x=actualCollectedTagPeak rho A x) ∧
    ∀ (rho : NONote) (A : CollectedPositiveNF) (a : Nat),
      (rho,A,a)∈collectedTagEntries tags →
      actualCollectedTagPeak rho A x≤actualCollectedMaximumPeak tags x

end LogicLineages.OrdinalComparison.Targets
