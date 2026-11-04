module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBetaApplicationEdgeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBetaApplicationEdgeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedQuotientApplication

theorem actualBetaApplicationEdge : NumberedBetaApplicationEdgeTargets.ActualBetaApplicationEdge := by
  intro n arity symbols S hc above Gamma sigma tau body a target hl ha hedge
  obtain ⟨rho,q,r,hq,hs,hcode,hr⟩ := hedge
  have hla := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity symbols S hc Gamma sigma tau (.lam body) a hl ha
  have hprimary := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    (applicationPacked (.lam body) a) ⟨rho,q⟩ hla hq).mp hcode.symm
  obtain ⟨f',a',he,hff,haa⟩ :=
    (NumberedPrimaryShapesProof.actualPrimaryApplicationComponents (Fin n) arity symbols S Gamma sigma tau (.lam body) a ⟨rho,q⟩).mp hprimary
  have htype : rho = tau := congrArg Sigma.fst he
  cases htype
  have hqeq : q = .app f' a' := by injection he
  subst q
  obtain ⟨body',hlameq,hbb⟩ :=
    (NumberedPrimaryLambdaBodyProof.actualPrimaryLambdaBody (Fin n) arity symbols S Gamma sigma tau body ⟨.arrow sigma tau,f'⟩).mp hff
  have hfeq : f' = .lam body' := by injection hlameq
  subst f'
  have hl' : InUniverse symbols S (.lam body') := ⟨hq.1.2.1,hq.2.1⟩
  have hb' : InUniverse symbols S body' := ⟨hl'.1.2.2,hl'.2⟩
  have hb : InUniverse symbols S body := ⟨hl.1.2.2,hl.2⟩
  have ha' : InUniverse symbols S a' := ⟨hq.1.2.2,hq.2.2⟩
  have hac := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma
    ⟨sigma,a⟩ ⟨sigma,a'⟩ ha ha').mpr haa
  rcases (NumberedLambdaRootProof.actualBetaApplicationStepCases (Fin n) arity symbols S above Gamma sigma tau body' a' r).mp hs with
    he | he | he | ⟨next,hstep,he⟩
  · subst r
    exact Or.inl hr.symm
  · subst r
    exact Or.inr (Or.inl ⟨body',a',hb',ha',hbb,haa,hr.symm⟩)
  · subst r
    have hbot : InUniverse symbols S (AuxTerm.bottom (Symbol := Fin n) (arity := arity) (Gamma := Gamma) (.arrow sigma tau)) := ⟨hl.1.1,trivial⟩
    exact Or.inr (Or.inr (Or.inl (hr.symm.trans
      (NumberedQuotientApplicationProof.representativeApplicationCongruence n arity symbols S hc Gamma sigma tau
        (.bottom (.arrow sigma tau)) (.bottom (.arrow sigma tau)) a' a hbot hbot ha' ha rfl hac.symm))))
  · subst r
    have hnext := NumberedWindowReductionProof.stepGood symbols S hc hstep hb'
    have hlnext : InUniverse symbols S (.lam next) := ⟨⟨hl.1.1,hl.1.2.1,hnext.1⟩,hnext.2⟩
    have hbc := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc (sigma :: Gamma)
      ⟨tau,body⟩ ⟨tau,body'⟩ hb hb').mpr hbb
    refine Or.inr (Or.inr (Or.inr ⟨next,hnext,⟨tau,body',next,hb',hstep,hbc.symm,rfl⟩,?_⟩))
    exact hr.symm.trans (NumberedQuotientApplicationProof.representativeApplicationCongruence n arity symbols S hc Gamma sigma tau
      (.lam next) (.lam next) a' a hlnext hlnext ha' ha rfl hac.symm)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBetaApplicationEdgeProof
