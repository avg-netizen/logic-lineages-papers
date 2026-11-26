module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedStepSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedSubstitutionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces
open NumberedPrimarySubstitution NumberedFiniteUniverse NumberedUniverseBindingTargets
open NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedVariableCount

theorem actualRankedPackedTraceSubstitution :
    NumberedRankedSubstitutionTargets.ActualRankedPackedTraceSubstitution := by
  intro Symbol arity symbols S above Gamma Delta theta count q r h
  induction h with
  | equivalent he =>
    refine ⟨0, Nat.le_refl 0, .equivalent
      (NumberedPrimarySubstitutionProof.substitutePrimary he Delta theta), ?_⟩
    intro _
    have hc := NumberedVariableCountProof.actualPrimaryVariableCount Symbol arity symbols S Gamma _ _ he
    simpa only [Nat.add_zero] using Nat.le_of_eq hc.symm
  | raw q r hs =>
    rcases NumberedRankedStepSubstitutionProof.substituteStep hs Delta theta with ⟨he,hlt⟩ | hstep
    · refine ⟨0, by omega, ?_, ?_⟩
      · change WindowTrace Symbol arity symbols S above Delta 0
          ⟨_,substitute q theta⟩ ⟨_,substitute r theta⟩
        rw [he]
        exact .equivalent (.refl _)
      · intro _
        change variableCount r + 1 ≤ variableCount q
        omega
    · exact ⟨1, Nat.le_refl 1, .raw _ _ hstep, by omega⟩
  | trans h1 h2 ih1 ih2 =>
    obtain ⟨m,hm,ht,hleft⟩ := ih1
    obtain ⟨k,hk,hu,hright⟩ := ih2
    refine ⟨m+k, by omega, .trans ht hu, ?_⟩
    intro hz
    have hmz : m = 0 := by omega
    have hkz : k = 0 := by omega
    have hl := hleft hmz
    have hr := hright hkz
    omega

theorem actualRankedPositiveQuotientSubstitution :
    NumberedRankedSubstitutionTargets.ActualRankedPositiveQuotientSubstitution := by
  intro n arity symbols S hc above Gamma Delta theta q r hq hr htheta hp
  obtain ⟨count,hpos,hcount⟩ :=
    (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma _ _).mp hp
  have ht := NumberedQuotientPathsProof.countedBackward n arity symbols S hc above Gamma count q r hq hr hcount
  obtain ⟨m,hm,hsub,hrank⟩ := actualRankedPackedTraceSubstitution
    (Fin n) arity symbols S above Gamma Delta theta count q r ht
  have hgood : InUniverse symbols S (substitutePacked theta q).2 :=
    NumberedUniverseBindingProof.actualSubstitution (Fin n) arity (fun t => t ∈ S)
      (HeadInWindow arity symbols S) Gamma Delta q.1 q.2 theta hq htheta
  have hpath := NumberedQuotientPathsProof.countedForward n arity symbols S hc above Delta m
    (substitutePacked theta q) (substitutePacked theta r) hgood hsub
  rcases NumberedQuotientPathsProof.pathDichotomy hpath with ⟨hz,he⟩ | hpositive
  · have hbound := hrank hz
    exact Or.inl ⟨he, by omega⟩
  · exact Or.inr hpositive

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedSubstitutionProof
