module
public import LogicLineages.ControlSensitivityCurrent.RawPlanComparisonTargets
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerSuccessProof
public import LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionTypedProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanComparison

open LogicLineages.OrdinalComparison.Source GroundEquivalence ExistentialPlan
open RawPlanComparisonTargets (encodeComparison)
open PlanCompiler

theorem typed_exactness : RawPlanComparisonTargets.TypedExactness := by
  intro Γ q
  have hrun : run (Γ.map SyntaxCode.typeCode) (encodePlan q) = some (encodeResult (compile q)) := by
    simp [run, PlanCompiler.typed_exactness]
  simp [compileComparisons, hrun, compareResult, encodeResult, RawPrimitiveGateTargets.encodeForest,
    DerivedComposition.aggregate_typed, DerivedComposition.wrap_typed,
    encodeComparison, strictPair, weakPair]

theorem success_reconstruction : RawPlanComparisonTargets.SuccessReconstruction := by
  intro context code out h
  obtain ⟨r, hr, _⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Γ,q,hΓ,hq,_⟩ := PlanCompiler.success_reconstruction context code r hr
  have ht := typed_exactness Γ q
  rw [hΓ, hq, h] at ht
  exact ⟨Γ,q,hΓ,hq,Option.some.inj ht⟩

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanComparison
