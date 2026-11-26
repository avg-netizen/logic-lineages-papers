import LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMapTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextChecks

namespace LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMapProof
open NumberedWindowSimulationData NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextTargets
open NumberedWindowPathWitnessChecks NumberedWindowCanonicalAddressMap NumberedWindowCanonicalAddressMapTargets

private theorem encodeInjective : Function.Injective encodeAddress := by
  intro a b equality
  have decoded := congrArg decodeAddress equality
  simpa only [NumberedWindowArithmeticClassAddressProof.round, Option.some.injEq] using decoded

theorem specification : ActualClassAddressSpecification := by
  intro S K Γ τ hk q
  have fibres := exact_ActualClassCodeFibers S K Γ τ hk
  have code : ActualCodeAt S K Γ τ (classCode hk q) q := Classical.choose_spec (fibres.1 q)
  refine ⟨code, ⟨Γ, τ, classCode hk q, q, rfl, code⟩, ?_⟩
  intro n hn
  have same := fibres.2.2 q _ _ code hn
  change encodeAddress ⟨Γ, τ, classCode hk q⟩ = encodeAddress ⟨Γ, τ, n⟩
  rw [same]

theorem injection : ActualClassAddressInjection := by
  intro S K Γ τ hk q r equality
  have fieldEq : (⟨Γ, τ, classCode hk q⟩ : ClassAddress) = ⟨Γ, τ, classCode hk r⟩ :=
    encodeInjective equality
  have sameCode := congrArg ClassAddress.least fieldEq
  have cq := (specification S K Γ τ hk q).1
  have cr := (specification S K Γ τ hk r).1
  have crAtQ : ActualCodeAt S K Γ τ (classCode hk q) r := by rw [sameCode]; exact cr
  exact (exact_ActualClassCodeFibers S K Γ τ hk).2.1 q r _ cq crAtQ

theorem successors : ActualClassAddressSuccessors := by
  intro S K Γ τ hk q n
  have cq := (specification S K Γ τ hk q).1
  constructor
  · intro edge
    obtain ⟨Δ, υ, i, j, x, y, source, target, xCode, yCode, path⟩ := edge
    have equalAddress : (⟨Δ, υ, i⟩ : ClassAddress) = ⟨Γ, τ, classCode hk q⟩ :=
      encodeInjective source
    cases equalAddress
    have same := (exact_ActualClassCodeFibers S K Γ τ hk).2.1 x q _ xCode cq
    subst x
    exact ⟨y, ((specification S K Γ τ hk y).2.2 j yCode).trans target, path⟩
  · rintro ⟨r, target, path⟩
    have cr := (specification S K Γ τ hk r).1
    exact ⟨Γ, τ, classCode hk q, classCode hk r, q, r, rfl, target, cq, cr, path⟩

end LogicLineages.PersistentMarking.NumberedWindowCanonicalAddressMapProof
