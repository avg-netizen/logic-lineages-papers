module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorArgumentAddresses
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorSelectComputabilityTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open Spine (ArrowPrefix)
open NumberedWindowArithmeticLeastClass NumberedWindowConstructorArgumentAddresses
open NumberedWindowExternalComputability
open NumberedWindowApplicationTargets (ArgsWindow)

def TypedAuxiliaryApplicationsComputable : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) ds τ q args out
    (hq : InWindow S K (finiteC Γ) (ArrowPrefix ds τ) q),
    ComputableClass S K Γ hk (ArrowPrefix ds τ) (classOf ⟨q, hq⟩) →
    ArgsWindow S K (finiteC Γ) ds args →
    (∀ a ∈ args.toList, ComputableArgument S K Γ hk a) → applications q args = some out →
    ∃ hw : InWindow S K (finiteC Γ) τ out, ComputableClass S K Γ hk τ (classOf ⟨out, hw⟩)

/-- The original full Select call is computable once its actual selected
occurrence and every actual lower-label owner copy are computable. -/
def SelectFromComputableCopies : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) f τ k bs es i selected ds out,
    (∀ q ∈ bs.toList, ComputableArgument S K Γ hk q) →
    (∀ q ∈ es.toList, ComputableArgument S K Γ hk q) →
    (bs.get i = some selected ∨ es.get i = some selected) →
    selected.type = ArrowPrefix ds τ →
    (∀ q ∈ (ownerCopies f k bs es ds).toList, ComputableArgument S K Γ hk q) →
    applications selected (ownerCopies f k bs es ds) = some out →
    ∃ hw : InWindow S K (finiteC Γ) τ out, ComputableClass S K Γ hk τ (classOf ⟨out, hw⟩)

end LogicLineages.PersistentMarking.NumberedWindowConstructorSelectComputabilityTargets
