import LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddresses
import LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetTargets

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorRawArgumentTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticAllContextTargets
open NumberedWindowConstructorArgumentAddresses NumberedWindowArithmeticDirectMultisetTargets

def RawStepPositiveAddresses : Prop :=
  ∀ S K Γ q r source target, DecisionSourceUniverse.Closed K →
    InWindow S K (finiteC Γ) q.type q → InWindow S K (finiteC Γ) r.type r → RawStep S K q r →
    slot S K Γ q = some source → slot S K Γ r = some target → AddressPositive S K source target

/-- Exactly one aligned occurrence is replaced by a genuine positive
descendant. The prefix and suffix are the actual canonical addresses. -/
def RawArgumentAddressDescent : Prop :=
  ∀ S K Γ source target sourceCodes targetCodes, DecisionSourceUniverse.Closed K →
    (∀ q ∈ source.toList, InWindow S K (finiteC Γ) q.type q) →
    (∀ q ∈ target.toList, InWindow S K (finiteC Γ) q.type q) → RawArgsStep S K source target →
    Slots S K Γ source sourceCodes → Slots S K Γ target targetCodes →
    AddressDirect S K sourceCodes targetCodes ∧
    ∃ prefix suffix : List Nat, ∃ before after : Nat,
      sourceCodes = prefix ++ before :: suffix ∧ targetCodes = prefix ++ after :: suffix ∧
        AddressPositive S K before after

end LogicLineages.PersistentMarking.NumberedWindowConstructorRawArgumentTargets
