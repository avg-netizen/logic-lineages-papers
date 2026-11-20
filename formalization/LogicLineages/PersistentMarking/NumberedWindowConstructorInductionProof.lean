import LogicLineages.PersistentMarking.NumberedWindowConstructorRepresentationProof

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorInductionProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData NumberedWindowArithmeticLeastClass
open NumberedWindowConstructorComputabilityTargets NumberedWindowConstructorRepresentationProof
open NumberedWindowConstructorArgumentAddresses NumberedWindowConstructorArgumentAddressChecks
open NumberedWindowConstructorOrderTargets NumberedWindowExternalComputability
open NumberedWindowPreservationGuardProof NumberedWindowConstructorHeadProfileChecks

theorem atClass {S K Γ hk τ q} (h : InWindow S K (finiteC Γ) τ q) (hc : ComputableArgument S K Γ hk q) :
    ComputableClass S K Γ hk τ (classOf ⟨q,h⟩) := by
  cases NumberedWindowApplicationDomainProof.annotation h.1
  exact hc.choose_spec

private theorem withHypothesis {S K Γ hk} (raws : RawCases S K Γ hk) (o : Owner) {bs es}
    (sb : Slots S K Γ o.base bs) (se : Slots S K Γ o.extras es)
    (hw : InWindow S K (finiteC Γ) o.term.type o.term)
    (mb : Members S K Γ hk o.base) (me : Members S K Γ hk o.extras)
    (ih : Hypothesis S K Γ hk (o.measure bs es)) : ComputableArgument S K Γ hk o.term := by
  refine ⟨hw, NumberedWindowExternalTypeFactsChecks.exact_NeutralComputability S K Γ o.term.type hk _ ?_ ?_⟩
  · apply (NumberedWindowExternalNeutralChecks.exact_ExactNonLambdaRepresentatives S K _ _ ⟨o.term,hw⟩).mpr
    cases o <;> intro σ body e <;> cases e
  · intro out edge
    obtain ⟨⟨q,hq⟩,⟨r,hr⟩,hqeq,rfl,raw⟩ := edge
    have hp := NumberedWindowExternalNeutralPrimaryProof.primaryOfClassEquality ⟨o.term,hw⟩ ⟨q,hq⟩ hqeq.symm
    have pe := exact_PrimaryHeadProfile S K Γ o.term.type o.term q hk hw hp
    obtain ⟨p,rfl⟩ := represented (pe.symm.trans (framed S K Γ o))
    have fe := Option.some.inj (((framed S K Γ o).symm.trans pe).trans (framed S K Γ p))
    obtain ⟨pb,px⟩ := members fe (annotated hq) mb me
    obtain ⟨b,bs',_⟩ := exact_ComputableArgumentsGiveMultiset S K Γ hk p.base pb
    obtain ⟨e,es',_⟩ := exact_ComputableArgumentsGiveMultiset S K Γ hk p.extras px
    have ihp : Hypothesis S K Γ hk (p.measure b e) := by
      intro n c d nc nd earlierStep nw nm ne
      exact ih n c d nc nd (earlier fe sb se bs' es' earlierStep) nw nm ne
    have hr' : InWindow S K (finiteC Γ) p.term.type r := by
      rw [NumberedWindowApplicationDomainProof.annotation hq.1]
      exact hr
    exact atClass hr (raws p b e bs' es' (annotated hq) pb px ihp r raw hr')

private def AtMeasure (S : Spine.Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (m : Measure) : Prop :=
  ∀ o : Owner, ∀ bs es, o.measure bs es = m → Slots S K Γ o.base bs → Slots S K Γ o.extras es →
    InWindow S K (finiteC Γ) o.term.type o.term → Members S K Γ hk o.base → Members S K Γ hk o.extras →
    ComputableArgument S K Γ hk o.term

theorem fromRaw : ConstructorInductionFromRawCases := by
  intro S K Γ hk raws
  have step : ∀ m, AdmittedMeasure S K m →
      (∀ n, AdmittedMeasure S K n → Earlier S K n m → AtMeasure S K Γ hk n) → AtMeasure S K Γ hk m := by
    rintro m _ predecessors o bs es rfl sb se hw mb me
    apply withHypothesis raws o sb se hw mb me
    intro p b e pb pe desc pw pm px
    exact predecessors _ (admitted p pb pe pw pm px) desc p b e rfl pb pe pw pm px
  intro o hw mb me
  obtain ⟨b,sb,_⟩ := exact_ComputableArgumentsGiveMultiset S K Γ hk o.base mb
  obtain ⟨e,se,_⟩ := exact_ComputableArgumentsGiveMultiset S K Γ hk o.extras me
  exact NumberedWindowConstructorOrderChecks.exact_ConstructorMeasureInduction S K _ step _ (admitted o sb se hw mb me)
    o b e rfl sb se hw mb me

end LogicLineages.PersistentMarking.NumberedWindowConstructorInductionProof
