module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowCanonicalAddressMap

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMapTargets
open NumberedWindowSimulationData NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextTargets
open NumberedWindowPathWitnessTargets NumberedWindowCanonicalAddressMap

def ActualClassAddressSpecification : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) τ),
    ActualCodeAt S K Γ τ (classCode hk q) q ∧
    AdmittedAddress S K (classAddress hk q) ∧
    ∀ n, ActualCodeAt S K Γ τ n q → classAddress hk q = encodeAddress ⟨Γ, τ, n⟩

def ActualClassAddressInjection : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K),
    Function.Injective (@classAddress S K Γ τ hk)

def ActualClassAddressSuccessors : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) τ) n,
    AddressPositive S K (classAddress hk q) n ↔
      ∃ r : Class S K (finiteC Γ) τ, classAddress hk r = n ∧ RS S K (finiteC Γ) τ q r

end LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMapTargets
