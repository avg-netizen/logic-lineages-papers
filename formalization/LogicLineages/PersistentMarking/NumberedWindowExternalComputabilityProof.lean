import LogicLineages.PersistentMarking.NumberedWindowExternalComputabilityTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalApplicationChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalComputabilityProof
open NumberedWindowExternalComputability NumberedWindowExternalComputabilityTargets
open NumberedWindowSimulationData NumberedWindowArithmeticLeastClass
open NumberedWindowExternalApplication NumberedWindowExternalApplicationChecks
open NumberedWindowPathWitnessChecks

theorem ground : GroundAtCanonicalAddress := by
  intro S K Γ hk q i hi
  constructor
  · rintro ⟨j,hj,h⟩
    obtain rfl := (exact_ActualClassCodeFibers S K Γ .ground hk).2.2 q j i hj hi
    exact h
  · exact fun h => ⟨i,hi,h⟩

theorem arrow : ArrowAtEveryTypedArgument := by
  intro S K Γ σ τ hk q
  rfl

theorem groundAcc {S K Γ} (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K (finiteC Γ) .ground) :
    ComputableClass S K Γ hk .ground q ↔ Acc (fun r q => RS S K (finiteC Γ) .ground q r) q := by
  obtain ⟨i,hi⟩ := (exact_ActualClassCodeFibers S K Γ .ground hk).1 q
  exact (ground S K Γ hk q i hi).trans (exact_ScalarClassAccessibility S K Γ .ground hk q i hi)

theorem positive : ComputablePositiveDescendants := by
  intro S K Γ τ hk
  induction τ with
  | ground =>
    intro q r step hq
    exact (groundAcc hk r).mpr (((groundAcc hk q).mp hq).inv step)
  | arrow σ τ _ codomain =>
    intro q r step hq u hu
    exact codomain (appClass hk q u) (appClass hk r u)
      (exact_QuotientAppPreservesPositive S K (finiteC Γ) σ τ hk q r u step) (hq u hu)

theorem direct : ComputableDirectDescendants := by
  intro S K Γ τ hk q r step hq
  exact positive S K Γ τ hk q r (.one step) hq

end LogicLineages.PersistentMarking.NumberedWindowExternalComputabilityProof
