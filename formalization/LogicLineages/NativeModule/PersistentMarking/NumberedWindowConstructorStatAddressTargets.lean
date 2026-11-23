module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorArgumentAddresses
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectMultisetTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorStatAddressTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticAllContextTargets
open NumberedWindowConstructorArgumentAddresses NumberedWindowArithmeticDirectMultisetTargets

def MarkDecreasePositiveAddresses : Prop :=
  ∀ S K Γ q r source target, DecisionSourceUniverse.Closed K →
    InWindow S K (finiteC Γ) q.type q → MarkDecrease q r →
    slot S K Γ q = some source → slot S K Γ r = some target → AddressPositive S K source target

/-- Primitive Stat replacement supplies genuine strict descent in the
canonical-address multiset. Only source arguments need to be admitted. -/
def PrimitiveReplacementAddressDescent : Prop :=
  ∀ S K Γ source target sourceCodes, DecisionSourceUniverse.Closed K →
    (∀ q ∈ source.toList, InWindow S K (finiteC Γ) q.type q) →
    PrimitiveReplacement source target → Slots S K Γ source sourceCodes →
    ∃ targetCodes, Slots S K Γ target targetCodes ∧ AddressDirect S K sourceCodes targetCodes

end LogicLineages.PersistentMarking.NumberedWindowConstructorStatAddressTargets
