import LogicLineages.PersistentMarking.NumberedWindowOriginalComputabilityFormulaTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMapChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalComputabilityChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorChecks

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalComputabilityFormulaChecks
open NumberedWindowOriginalComputabilityFormulaTargets NumberedWindowApplicationGraphChecks
open NumberedWindowCanonicalAddressMapChecks NumberedWindowCanonicalAddressMap
open NumberedWindowExternalComputabilityChecks NumberedWindowExternalIDOperatorChecks
open NumberedWindowExternalApplication NumberedWindowArithmeticClassAddress
open NumberedWindowComputabilityReading

theorem exact_ExactClassComputabilityReading : ExactClassComputabilityReading := by
  intro S K Γ hk τ
  induction τ with
  | ground =>
    intro q i hi
    exact (exact_ActualLeastTagProjection S K _).1.trans ((exact_GroundAtCanonicalAddress S K Γ hk q i hi).symm)
  | arrow σ τ ihσ ihτ =>
    intro q i hi
    rw [exact_ArrowAtEveryTypedArgument]
    constructor
    · intro h u cu
      let j := classCode hk u
      let k := classCode hk (appClass hk q u)
      have hj := (exact_ActualClassAddressSpecification S K Γ σ hk u).1
      have hk' := (exact_ActualClassAddressSpecification S K Γ τ hk (appClass hk q u)).1
      apply (ihτ _ k hk').mp
      apply h (encodeAddress ⟨Γ,σ,j⟩)
      · apply (exact_ClassApplicationGraph S K Γ σ τ hk q i hi _ _).mpr
        exact ⟨j,u,k,rfl,hj,rfl,hk'⟩
      · exact (ihσ u j hj).mpr cu
    · intro h a v ha ca
      obtain ⟨j,u,k,rfl,hj,rfl,hk'⟩ :=
        (exact_ClassApplicationGraph S K Γ σ τ hk q i hi a v).mp ha
      exact (ihτ _ k hk').mpr (h u ((ihσ u j hj).mp ca))

#print axioms exact_ExactClassComputabilityReading
end LogicLineages.PersistentMarking.NumberedWindowOriginalComputabilityFormulaChecks
