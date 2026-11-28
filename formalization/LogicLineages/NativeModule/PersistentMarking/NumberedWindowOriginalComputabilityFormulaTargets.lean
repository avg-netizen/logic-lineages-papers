module

public import LogicLineages.PersistentMarking.NumberedWindowComputabilityReading
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationGraphTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalComputability

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalComputabilityFormulaTargets
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowAddressApplication (graph)
open NumberedWindowExternalIDOperators NumberedWindowArithmeticLeastClass
open NumberedWindowSimulationData NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticClassAddress NumberedWindowExternalComputability
open NumberedWindowComputabilityReading (holds)

def formulaType : Ty → LogicLineages.OrdinalComparison.Source.Ty
  | .ground => .ground
  | .arrow σ τ => .arrow (formulaType σ) (formulaType τ)

def ExactClassComputabilityReading : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) τ (q : Class S K (finiteC Γ) τ) i,
  ActualCodeAt S K Γ τ i q →
    (holds (fun a u v => graph (fixed S K) a u v = true) (Least (taggedStep S K))
        (formulaType τ) (encodeAddress ⟨Γ,τ,i⟩) ↔ ComputableClass S K Γ hk τ q)

end LogicLineages.PersistentMarking.NumberedWindowOriginalComputabilityFormulaTargets
