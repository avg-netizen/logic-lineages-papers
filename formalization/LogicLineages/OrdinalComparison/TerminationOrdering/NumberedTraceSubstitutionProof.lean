module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSubstitutionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedPrimarySubstitution

theorem actualPackedTraceSubstitution : NumberedTraceSubstitutionTargets.ActualPackedTraceSubstitution := by
  intro Symbol arity symbols S above Gamma Delta theta count q r h
  induction h with
  | equivalent he =>
    exact ⟨0,Nat.le_refl 0,.equivalent (NumberedPrimarySubstitutionProof.substitutePrimary he Delta theta)⟩
  | raw q r hs =>
    rcases NumberedStepSubstitutionProof.substituteStep hs Delta theta with he | hstep
    · refine ⟨0,by omega,?_⟩
      change WindowTrace Symbol arity symbols S above Delta 0 ⟨_,substitute q theta⟩ ⟨_,substitute r theta⟩
      rw [he]
      exact .equivalent (.refl _)
    · exact ⟨1,Nat.le_refl 1,.raw _ _ hstep⟩
  | trans h1 h2 ih1 ih2 =>
    obtain ⟨m,hm,ht⟩ := ih1
    obtain ⟨k,hk,hu⟩ := ih2
    exact ⟨m+k,by omega,.trans ht hu⟩

theorem actualTypedTraceSubstitution : NumberedTraceSubstitutionTargets.ActualTypedTraceSubstitution := by
  intro Symbol arity symbols S above Gamma Delta theta tau count q r h
  have hp := (NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above Gamma tau count q r).mpr h
  obtain ⟨m,hm,ht⟩ := actualPackedTraceSubstitution Symbol arity symbols S above Gamma Delta theta count ⟨tau,q⟩ ⟨tau,r⟩ hp
  exact ⟨m,hm,(NumberedWindowTracesProof.typedPresentation Symbol arity symbols S above Delta tau m
    (substitute q theta) (substitute r theta)).mp ht⟩

theorem actualTupleTraceSubstitution : NumberedTraceSubstitutionTargets.ActualTupleTraceSubstitution := by
  intro Symbol arity symbols S above Gamma Delta theta types count base target h
  induction h with
  | equivalent he =>
    exact ⟨0,Nat.le_refl 0,.equivalent
      (NumberedPrimarySubstitutionProof.actualArgumentPrimarySubstitution Symbol arity symbols S Gamma Delta _ theta _ _ he)⟩
  | raw hs =>
    rcases NumberedStepSubstitutionProof.actualArgumentStepSubstitution Symbol arity symbols S above Gamma Delta theta _ _ _ hs with he | hstep
    · refine ⟨0,by omega,?_⟩
      rw [he]
      exact .equivalent (NumberedWindowTracesProof.argumentReflexivity _)
    · exact ⟨1,Nat.le_refl 1,.raw hstep⟩
  | trans h1 h2 ih1 ih2 =>
    obtain ⟨m,hm,ht⟩ := ih1
    obtain ⟨k,hk,hu⟩ := ih2
    exact ⟨m+k,by omega,.trans ht hu⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceSubstitutionProof
