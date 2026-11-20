import LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddresses

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddressTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticFields NumberedWindowExternalIDOperators
open NumberedWindowConstructorArgumentAddresses NumberedWindowArithmeticAllContextTargets

def PrimaryArgumentAddress : Prop :=
  ∀ S K Γ τ q r, DecisionSourceUniverse.Closed K →
    InWindow S K (finiteC Γ) τ q → InWindow S K (finiteC Γ) τ r → Primary S K (finiteC Γ) τ q r →
    slot S K Γ q = slot S K Γ r

def PermutedArgumentAddresses : Prop :=
  ∀ S K Γ (xs ys : NArgs) cs ds, xs.toList.Perm ys.toList →
    Slots S K Γ xs cs → Slots S K Γ ys ds → cs.Perm ds

def ComputableArgumentsGiveMultiset : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) (xs : NArgs),
    (∀ q ∈ xs.toList, ComputableArgument S K Γ hk q) →
    ∃ cs, Slots S K Γ xs cs ∧ (∀ c ∈ cs, Least (scalarStep S K) c) ∧
      Least (multisetStep S K) (encodeFields cs)

end LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddressTargets
