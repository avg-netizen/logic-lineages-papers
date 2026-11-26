module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWindowSubstitutionRawProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalWindowSubstitutionChecks
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowExternalWindowSubstitutionTargets
open NumberedWindowPreservationGuardProof (annotated)
open NumberedWindowPreservationBoundProof (one)
open NumberedWindowPreservationSubstitutionProof (term)

theorem exact_SubstitutionWindowStep : SubstitutionWindowStep := by
  intro S K C D τ q r values depth hk hc hStep
  rcases NumberedWindowExternalWindowSubstitutionRawProof.skeleton hk hStep.1
    values depth C D hc (annotated hStep.2.1) with hRaw | hCollapse
  · exact .inl ⟨hRaw, term S K hk values depth C D q τ hStep.2.1 hc,
      term S K hk values depth C D r τ hStep.2.2 hc⟩
  · exact .inr hCollapse

theorem exact_FreeSubstitutionWindowStep : FreeSubstitutionWindowStep := by
  intro S K C σ τ q r name hk hσ hStep
  have hFree : InWindow S K C σ (.free σ name) :=
    ⟨.free, hk σ hσ, fun _ hm => (List.not_mem_nil hm).elim⟩
  rcases exact_SubstitutionWindowStep S K (C.push σ) C τ q r (.cons (.free σ name) .nil) 0
    hk (one hk hFree) hStep with hLift | ⟨_, ρ, hm⟩
  · exact hLift
  · have hImpossible : NTerm.bottom ρ = .free σ name := List.mem_singleton.mp hm
    cases hImpossible

#print axioms exact_SubstitutionWindowStep
#print axioms exact_FreeSubstitutionWindowStep

end LogicLineages.PersistentMarking.NumberedWindowExternalWindowSubstitutionChecks
