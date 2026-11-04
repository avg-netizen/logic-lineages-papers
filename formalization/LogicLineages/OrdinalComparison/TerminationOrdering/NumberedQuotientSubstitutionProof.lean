module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientSubstitutionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets
open NumberedPrimarySubstitution NumberedLeastCodeRepresentative NumberedQuotientPaths

theorem actualCountedQuotientSubstitution : NumberedQuotientSubstitutionTargets.ActualCountedQuotientSubstitution := by
  intro n arity symbols S hc above Gamma Delta theta q r hq hr htheta count hp
  have ht := NumberedQuotientPathsProof.countedBackward n arity symbols S hc above Gamma count q r hq hr hp
  obtain ⟨m,hm,hsub⟩ := NumberedTraceSubstitutionProof.actualPackedTraceSubstitution
    (Fin n) arity symbols S above Gamma Delta theta count q r ht
  have hgood : InUniverse symbols S (substitutePacked theta q).2 :=
    NumberedUniverseBindingProof.actualSubstitution (Fin n) arity (fun t => t ∈ S)
      (HeadInWindow arity symbols S) Gamma Delta q.1 q.2 theta hq htheta
  exact ⟨m,hm,NumberedQuotientPathsProof.countedForward n arity symbols S hc above Delta m
    (substitutePacked theta q) (substitutePacked theta r) hgood hsub⟩

theorem actualPositiveQuotientSubstitution : NumberedQuotientSubstitutionTargets.ActualPositiveQuotientSubstitution := by
  intro n arity symbols S hc above Gamma Delta theta q r hq hr htheta hp
  obtain ⟨count,hpos,hcount⟩ := (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma _ _).mp hp
  obtain ⟨m,hm,hsub⟩ := actualCountedQuotientSubstitution n arity symbols S hc above Gamma Delta theta q r
    hq hr htheta count hcount
  rcases NumberedQuotientPathsProof.pathDichotomy hsub with ⟨hz,he⟩ | hpositive
  · exact Or.inl he
  · exact Or.inr hpositive

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientSubstitutionProof
