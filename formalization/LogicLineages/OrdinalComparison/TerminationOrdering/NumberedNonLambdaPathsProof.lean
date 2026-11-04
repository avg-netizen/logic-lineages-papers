module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaPathsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaPathsProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryShapes
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedQuotientApplication

theorem actualPositiveFirstEdge : NumberedNonLambdaPathsTargets.ActualPositiveFirstEdge := by
  intro H x y
  constructor
  · intro h
    induction h with
    | step h => exact ⟨_,h,Or.inl rfl⟩
    | trans h k ih ik =>
      obtain ⟨z,hz,he | hp⟩ := ih
      · subst z
        exact ⟨_,hz,Or.inr k⟩
      · exact ⟨z,hz,Or.inr (.trans hp k)⟩
  · rintro ⟨z,hz,he | hp⟩
    · subst z
      exact .step hz
    · exact .trans (.step hz) hp

theorem actualNonLambdaApplicationPath : NumberedNonLambdaPathsTargets.ActualNonLambdaApplicationPath := by
  intro n arity symbols S hc above Gamma sigma tau f a target hf ha hn hp
  obtain ⟨z,hz,he⟩ := (actualPositiveFirstEdge _ _ _).mp hp
  rcases NumberedNonLambdaApplicationProof.actualNonLambdaApplicationEdge n arity symbols S hc above
    Gamma sigma tau f a z hf ha hn hz with hb | ⟨g,hg,hfg,hgcode⟩
  · have hfa := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity symbols S hc Gamma sigma tau f a hf ha
    have ht := NumberedUniverseOperationsProof.rootType (fun t => t ∈ S) (HeadInWindow arity symbols S) (.app f a) hfa
    rcases he with he | hr
    · exact Or.inl (he.symm.trans hb)
    · rw [hb] at hr
      exact False.elim (NumberedBottomAccessibilityProof.actualBottomPositiveTerminal n arity symbols S hc above Gamma tau ht target hr)
  · exact Or.inr ⟨g,hg,hfg,by simpa only [hgcode] using he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaPathsProof
