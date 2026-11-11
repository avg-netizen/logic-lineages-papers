module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedReplacementProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedEdgeProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowReduction NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedQuotientPaths
open SourceZeroNumberedComputability SourceZeroNumberedShapeProof SourceZeroNumberedReplacementProof

theorem actualZeroNumberedEdge : SourceZeroNumberedComputabilityTargets.ActualZeroNumberedEdge := by
  intro n arity symbols S hc above Gamma f tau base types extras y hsource hedge
  obtain ⟨rho,q,r,hq,hs,hcode,hr⟩ := hedge
  have hp := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    ⟨tau,.numbered 0 f tau base types extras⟩ ⟨rho,q⟩ hsource hq).mp hcode.symm
  have ht : tau = rho := NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma _ _
    (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma _ _ hp)
  cases ht
  have hl := primaryLabel hp
  have hm := primaryMembers hc hp hsource
  cases q with
  | numbered k g tau base' types' extras' =>
    have hk : k = 0 := Option.some.inj hl.symm
    subst k
    rcases (actualZeroNumberedStep (Fin n) arity symbols S above Gamma g tau base' types' extras' r).mp hs with
      he | ⟨target,hstep,he⟩ | ⟨target,hstep,he⟩
    · subst r
      exact Or.inl hr.symm
    · subst r
      refine Or.inr ⟨g,target,types',extras',NumberedWindowReductionProof.stepGood symbols S hc hs hq,hr.symm,?_⟩
      exact replacementPerm hm (List.Perm.refl _)
        (replacementAppendRight (argumentStepReplacement hstep ⟨hq.1.2.1,hq.2.2.1⟩) (argumentCodes symbols S extras'))
    · subst r
      refine Or.inr ⟨g,base',types',target,NumberedWindowReductionProof.stepGood symbols S hc hs hq,hr.symm,?_⟩
      exact replacementPerm hm (List.Perm.refl _)
        (replacementAppendLeft (argumentStepReplacement hstep ⟨hq.1.2.2,hq.2.2.2⟩) (argumentCodes symbols S base'))
  | var => cases hl
  | lam => cases hl
  | app => cases hl
  | bottom => cases hl
  | ordinary => cases hl
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedEdgeProof
