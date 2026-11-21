module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBackwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets
open NumberedWindowInternalSparseApplicationFrontendOpenForwardProof (forward)
open NumberedWindowInternalSparseApplicationFrontendOpenBackwardProof (backward)

theorem exact_OpenGuardedApplication : ExactOpenGuardedApplication := by
  intro body i least α Γ f u y
  let accepted := programGraph (applicationGuard i least) (suc z) ![f,u,y]
  let report := applicationReport i least f u y
  obtain ⟨yes⟩ := forward (body := body) (Γ := accepted :: Γ) i least f u y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨rev⟩ := backward (body := body) (Γ := report :: Γ) i least f u y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction rev)⟩

#print axioms exact_OpenGuardedApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenChecks
