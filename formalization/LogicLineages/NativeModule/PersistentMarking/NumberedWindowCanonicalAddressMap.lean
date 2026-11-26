module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPathWitnessChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMap
open NumberedWindowSimulationData NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticClassAddress NumberedWindowPathWitnessChecks

noncomputable def classCode {S K Γ τ} (hk : DecisionSourceUniverse.Closed K)
    (x : Class S K (finiteC Γ) τ) : Nat :=
  Classical.choose ((exact_ActualClassCodeFibers S K Γ τ hk).1 x)

noncomputable def classAddress {S K Γ τ} (hk : DecisionSourceUniverse.Closed K)
    (x : Class S K (finiteC Γ) τ) : Nat :=
  encodeAddress ⟨Γ, τ, classCode hk x⟩

end LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMap
