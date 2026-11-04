module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientWeakeningTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientWeakeningProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedPrimaryWeakening

theorem actualCountedWeakeningReflection : NumberedQuotientWeakeningTargets.ActualCountedWeakeningReflection := by
  intro n arity symbols S hc above Gamma sigma q hq count target hp
  have hw : InUniverse symbols S (renamePacked (Renaming.weaken Gamma sigma) q).2 :=
    NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ S) (HeadInWindow arity symbols S)
      Gamma (sigma :: Gamma) q.1 q.2 (Renaming.weaken Gamma sigma) hq
  obtain ⟨r,hr,hcode,htrace⟩ := NumberedQuotientPathsProof.liftPath symbols S hc above (sigma :: Gamma) hp
    (renamePacked (Renaming.weaken Gamma sigma) q) hw rfl
  obtain ⟨r0,he,hback⟩ := NumberedTraceWeakeningProof.actualPackedTraceWeakeningReflection
    (Fin n) arity symbols S above Gamma sigma count q r htrace
  have hr0 : InUniverse symbols S r0.2 := NumberedWindowTracesProof.endpoint hc hback hq
  refine ⟨r0,hr0,?_,?_⟩
  · exact (congrArg (representativeCode symbols S) he).trans hcode
  · exact NumberedQuotientPathsProof.countedForward n arity symbols S hc above Gamma count q r0 hq hback

theorem actualPositiveWeakeningReflection : NumberedQuotientWeakeningTargets.ActualPositiveWeakeningReflection := by
  intro n arity symbols S hc above Gamma sigma q hq target hp
  obtain ⟨count,hpos,hcount⟩ := (NumberedQuotientPathsProof.positiveClosure n arity symbols S above (sigma :: Gamma) _ _).mp hp
  obtain ⟨r,hr,hcode,hback⟩ := actualCountedWeakeningReflection n arity symbols S hc above Gamma sigma q hq count target hcount
  exact ⟨r,hr,hcode,(NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma _ _).mpr ⟨count,hpos,hback⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientWeakeningProof
