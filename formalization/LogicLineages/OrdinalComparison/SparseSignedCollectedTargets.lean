module
public import LogicLineages.OrdinalComparison.SparseSignedCollectedDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualCollectedTagPeakIndexCalibration : Prop :=
  ∀ (rho : NONote) (A : CollectedPositiveNF), Order.IsSuccLimit rho.1.repr →
    rho.1.repr<epsilonZero → CollectedPositiveValid A → collectedPositiveSupport A=true →
    ∀ x : Nat, 2≤x →
      let s := actualCollectedTagPeakIndex rho A x
      x≤s ∧ actualCollectedTagPeak rho A x=Phi s ∧
      Phi s<actualProfileHead rho (actualCollectedPositiveEval A x) ∧
      actualProfileHead rho (actualCollectedPositiveEval A x)<2*Phi s

/-- Actual signed-row supplier. Distinct peaks are an explicit local premise;
the eventual finite-zero theorem must discharge it by reachable-height induction. -/
def SparseSignedCollectedNonzero : Prop :=
  ∀ (row : SignedCollectedRow) (p q : Int) (x : Nat), SignedCollectedValid row → row≠[] →
    row.Pairwise (fun a b => actualCollectedTagPeak a.1.1 a.1.2 x≠
      actualCollectedTagPeak b.1.1 b.1.2 x) →
    signedCollectedRowBound row p q≤x →
    actualSignedCollectedValue row x+p*(x : Int)+q≠0

end LogicLineages.OrdinalComparison.Targets
