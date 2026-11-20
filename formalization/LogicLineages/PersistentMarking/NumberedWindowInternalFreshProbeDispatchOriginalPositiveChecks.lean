import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalFreshProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowSupportChecks

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalPositiveChecks
open NumberedWindowInternalFreshProbeDispatchOriginalPositiveTargets
open NumberedWindowInternalFreshProbeDispatchOriginalWindowSupportChecks
  (exact_OriginalTypeSupport exact_OriginalWindowChild)
open NumberedWindowProbeCode (code)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open NumberedWindowArithmeticTyCode (encodeTy)

theorem exact_OriginalFreshApplication : ExactOriginalFreshApplication :=
  NumberedWindowInternalFreshProbeDispatchOriginalFreshProof.fresh

private def localTy : LogicLineages.OrdinalComparison.Source.Ty → Ty
  | .ground => .ground
  | .arrow σ τ => .arrow (localTy σ) (localTy τ)

private theorem formulaLocal (τ : LogicLineages.OrdinalComparison.Source.Ty) :
    formulaType (localTy τ) = τ := by
  induction τ with
  | ground => rfl
  | arrow σ τ ihσ ihτ => simp only [localTy,formulaType,ihσ,ihτ]

private theorem originalCode (τ : Ty) : code (formulaType τ) = encodeTy τ := by
  induction τ with
  | ground => rfl
  | arrow σ τ ihσ ihτ =>
    simp only [formulaType,code,encodeTy,ihσ,ihτ,NumberedWindowActualPairAlgorithmChecks.currentPair]

private theorem sourceCode (τ : LogicLineages.OrdinalComparison.Source.Ty) :
    code τ = encodeTy (localTy τ) := by
  simpa only [formulaLocal] using originalCode (localTy τ)

theorem exact_OriginalNumericalTotal : ExactOriginalNumericalTotal := by
  intro S K hk σ τ f h
  rw [sourceCode] at h
  obtain ⟨_,_,_,u,v,_,_,_,_,hp,hg,ht⟩ :=
    exact_OriginalFreshApplication S K hk (localTy σ) (localTy τ) f h
  exact ⟨u,v,hp,hg,by rwa [sourceCode]⟩

theorem exact_OriginalValidWindow : ExactOriginalValidWindow := by
  intro S K hk
  exact ⟨exact_OriginalTypeSupport S K,exact_OriginalWindowChild K hk,exact_OriginalNumericalTotal S K hk⟩

#print axioms exact_OriginalFreshApplication
#print axioms exact_OriginalNumericalTotal
#print axioms exact_OriginalValidWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalPositiveChecks
