module
public import LogicLineages.OrdinalComparison.CollectedAffineBandDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def PhiMultiplicativeStepGap : Prop :=
  ∀ s k : Nat, k≤s → k*Phi s<Phi (s+1)

def PhiBetweenImagesRoot : Prop :=
  ∀ s n : Nat, Phi s<n → n<Phi (s+1) → ControlRoot n

def CollectedAffineInputBand : Prop :=
  ∀ (rho : NONote) (c b : Nat), Order.IsSuccLimit rho.1.repr → rho.1.repr<epsilonZero → 1≤b →
    collectedAffineThreshold rho c b=max 4 (actualOrdinalNorm rho.1.repr+c+b+1) ∧
    ∀ x : Nat, collectedAffineThreshold rho c b≤x →
      x≤actualOrdinalNorm (actualCollectedTagInput rho (.mk c b .nil) x) ∧
      actualOrdinalNorm (actualCollectedTagInput rho (.mk c b .nil) x)<Phi x

end LogicLineages.OrdinalComparison.Targets
