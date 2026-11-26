import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppProof
import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationClassProof

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppGraphChecks
open NumberedWindowInternalFreshProbeDispatchCanonicalAppTargets
open NumberedWindowInternalFreshProbeDispatchCanonicalAppProof (exact_CanonicalLiteralApplication)
open NumberedWindowAddressApplication (graph)
open NumberedWindowArithmeticAllContextAdmittedProof (canonical)

theorem exact_CanonicalLiteralApplicationGraph : ExactCanonicalLiteralApplicationGraph := by
  intro S K Γ σ τ hk q u i j hq hu v
  have qb := (canonical S K ⟨Γ,.arrow σ τ,i⟩ hk).mpr ⟨q,hq⟩
  have ub := (canonical S K ⟨Γ,σ,j⟩ hk).mpr ⟨u,hu⟩
  have bridge := NumberedWindowAddressApplicationClassProof.classExact
    S K Γ σ τ hk q u i j hq hu v
  rw [graph,exact_CanonicalLiteralApplication S K Γ σ τ i j qb ub]
  constructor
  · intro h
    exact bridge.mp (eq_of_beq h)
  · intro h
    rw [bridge.mpr h]
    simp

#print axioms exact_CanonicalLiteralApplicationGraph
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppGraphChecks
