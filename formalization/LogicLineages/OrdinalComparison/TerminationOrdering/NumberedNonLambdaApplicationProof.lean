module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaApplicationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaApplicationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedWindowEquivalence NumberedPrimaryShapes
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedQuotientApplication

theorem actualNonLambdaApplicationStep : NumberedNonLambdaApplicationTargets.ActualNonLambdaApplicationStep := by
  intro Symbol arity symbols S above Gamma sigma tau f a q hn
  constructor
  · intro h
    cases h with
    | appFunction f g a hs => exact Or.inr ⟨g,hs,rfl⟩
    | beta body a => cases hn
    | bottom q h => exact Or.inl rfl
  · intro h
    rcases h with he | ⟨g,hs,he⟩
    · subst q
      exact .bottom (.app f a) (by intro h; cases h)
    · subst q
      exact .appFunction f g a hs

theorem actualNonLambdaApplicationEdge : NumberedNonLambdaApplicationTargets.ActualNonLambdaApplicationEdge := by
  intro n arity symbols S hc above Gamma sigma tau f a target hf ha hn hedge
  obtain ⟨rho,q,r,hq,hs,hcode,hr⟩ := hedge
  have hfa := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity symbols S hc Gamma sigma tau f a hf ha
  have hprimary := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    (applicationPacked f a) ⟨rho,q⟩ hfa hq).mp hcode.symm
  obtain ⟨f',a',he,hff,haa⟩ :=
    (NumberedPrimaryShapesProof.actualPrimaryApplicationComponents (Fin n) arity symbols S Gamma sigma tau f a ⟨rho,q⟩).mp hprimary
  have htype : rho = tau := congrArg Sigma.fst he
  cases htype
  have hqeq : q = .app f' a' := by injection he
  subst q
  have hf' : InUniverse symbols S f' := ⟨hq.1.2.1,hq.2.1⟩
  have ha' : InUniverse symbols S a' := ⟨hq.1.2.2,hq.2.2⟩
  have hn' : isLambda f' = false :=
    (NumberedPrimaryShapesProof.actualPrimaryLambdaShape (Fin n) arity symbols S Gamma _ _ hff).symm.trans hn
  rcases (actualNonLambdaApplicationStep (Fin n) arity symbols S above Gamma sigma tau f' a' r hn').mp hs with he | ⟨g,hfg,he⟩
  · subst r
    exact Or.inl hr.symm
  · subst r
    have hg := NumberedWindowReductionProof.stepGood symbols S hc hfg hf'
    have hfc := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
      ⟨.arrow sigma tau,f⟩ ⟨.arrow sigma tau,f'⟩ hf hf').mpr hff
    have hac := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
      ⟨sigma,a⟩ ⟨sigma,a'⟩ ha ha').mpr haa
    refine Or.inr ⟨g,hg,⟨.arrow sigma tau,f',g,hf',hfg,hfc.symm,rfl⟩,?_⟩
    exact hr.symm.trans (NumberedQuotientApplicationProof.representativeApplicationCongruence n arity symbols S hc
      Gamma sigma tau g g a' a hg hg ha' ha rfl hac.symm)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaApplicationProof
