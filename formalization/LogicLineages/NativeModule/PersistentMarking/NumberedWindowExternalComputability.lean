module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalApplication
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDOperators

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalComputability
open Spine NumberedWindowSimulationData NumberedWindowExternalApplication
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticClassAddress
open NumberedWindowExternalIDOperators NumberedWindowPathWitnessTargets

/-- Type recursion for (T) in a single finite source context. Ground
membership uses the genuine canonical external scalar predicate of (A). -/
def ComputableClass (S : Signature) (K : List Ty) (Γ : List Ty)
    (hk : DecisionSourceUniverse.Closed K) : (τ : Ty) → Class S K (finiteC Γ) τ → Prop
  | .ground, q => ∃ i, ActualCodeAt S K Γ .ground i q ∧
      Least (scalarStep S K) (encodeAddress ⟨Γ,.ground,i⟩)
  | .arrow σ τ, q => ∀ u : Class S K (finiteC Γ) σ, ComputableClass S K Γ hk σ u →
      ComputableClass S K Γ hk τ (appClass hk q u)

end LogicLineages.PersistentMarking.NumberedWindowExternalComputability
