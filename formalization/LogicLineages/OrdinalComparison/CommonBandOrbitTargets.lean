module
public import LogicLineages.OrdinalComparison.CommonBandOrbitDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CommonBandOrbitCancellation : Prop :=
  ∀ x t u L J : Nat, CommonBandOrRoot x t → CommonBandOrRoot x u →
    (Phi^[L]) t=(Phi^[J]) u → L=J ∧ t=u

def ActualCommonBandPeakInjectivity : Prop :=
  ∀ (a b : Ordinal.{0}) (x : Nat), a<epsilonZero → b<epsilonZero →
    Ordinal.omega0≤a → Ordinal.omega0≤b →
    CommonBandOrRoot x (actualOrdinalNorm a) → CommonBandOrRoot x (actualOrdinalNorm b) →
    actualTerminalValue a=actualTerminalValue b → a=b

end LogicLineages.OrdinalComparison.Targets
