module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalProbeTotalTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTypedProbeChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowActualPairAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalProbeTotalChecks
open NumberedWindowOriginalProbeTotalTargets NumberedWindowProbeCode
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open NumberedWindowArithmeticTyCode (encodeTy)

theorem exact_FormulaTypeCoding : ExactFormulaTypeCoding := by
  intro τ
  induction τ with
  | ground => rfl
  | arrow σ τ ihσ ihτ => simp [formulaType,code,encodeTy,ihσ,ihτ,NumberedWindowActualPairAlgorithmChecks.currentPair]

private def original : LogicLineages.OrdinalComparison.Source.Ty → Ty
  | .ground => .ground
  | .arrow σ τ => .arrow (original σ) (original τ)

private theorem back (τ : LogicLineages.OrdinalComparison.Source.Ty) : formulaType (original τ) = τ := by
  induction τ with
  | ground => rfl
  | arrow σ τ ihσ ihτ => simp [original,formulaType,ihσ,ihτ]

private theorem exactCode (τ : LogicLineages.OrdinalComparison.Source.Ty) :
    code τ = encodeTy (original τ) := by
  simpa only [back] using exact_FormulaTypeCoding (original τ)

theorem exact_OriginalProbeTotal : OriginalProbeTotal := by
  intro S K hk σ τ f h
  rw [exactCode] at h
  obtain ⟨_,_,_,u,v,_,_,_,_,value,application,result⟩ :=
    NumberedWindowTypedProbeChecks.exact_FreshProbeApplication S K hk (original σ) (original τ) f h
  exact ⟨u,v,value,application,by rwa [exactCode]⟩

#print axioms exact_FormulaTypeCoding
#print axioms exact_OriginalProbeTotal
end LogicLineages.PersistentMarking.NumberedWindowOriginalProbeTotalChecks
