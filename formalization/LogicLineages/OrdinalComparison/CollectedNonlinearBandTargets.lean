module
public import LogicLineages.OrdinalComparison.CollectedNonlinearBandDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedNonlinearInputBand : Prop :=
  ∀ (rho : NONote) (c b : Nat) (tags : CollectedPositiveTags),
    Order.IsSuccLimit rho.1.repr → rho.1.repr<epsilonZero → CollectedTagsValid tags → tags≠.nil →
    collectedNonlinearThreshold rho c b tags=
      max 4 (max (actualOrdinalNorm rho.1.repr+c+b) (2*collectedCoefficientSum tags+1)) ∧
    ∀ x : Nat, collectedNonlinearThreshold rho c b tags≤x →
      let t := actualOrdinalNorm (actualCollectedTagInput rho (.mk c b tags) x)
      let Y := actualCollectedMaximumPeak tags x
      let C := collectedCoefficientSum tags
      Phi x<t ∧ ControlRoot t ∧
      ∃ s : Nat, Y=Phi s ∧ Y<t ∧ t<(2*C+1)*Y ∧ (2*C+1)*Y<Phi (s+1)

end LogicLineages.OrdinalComparison.Targets
