module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SelectStageSoundnessTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SelectStageSoundnessProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice RecursiveComparison ConstructorInputLogicalRelation ActualComparisonCompleteness ActualComparisonCompletenessSupportProof RelatedOccurrenceMatching ActualValueLogicalRelation OrdinaryFunctionalValue CopyStatStageSoundness CopyStatStageSoundnessProof MarkedSelectTest TypedObservationAccess

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem selectedRelated (above : Symbol → Symbol → Prop) (f : HeadIndex I) (P : World I) (a : Inputs I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types)
    (ha : InputRelated I above f P a base extras) (p : TypedExtraDownsets.Packed I P) (hp : Selected f a p) :
    ∃ q ∈ argumentList base++argumentList extras,PackedRelated I above P p q := by
  rcases hp with hb | he
  · have H := packedArgumentsRelated above P (headArguments arity f.val)
      (CoherentConstructorLatticeProof.headBaseTypes Symbol inferInstance arity I f) a.1 base ha.1
    obtain ⟨q,hq,hr⟩ := leftWitness H hb
    exact ⟨q,List.mem_append_left _ hq,hr⟩
  · obtain ⟨q,hq,hr⟩ := ha.2 p he
    exact ⟨q,List.mem_append_right _ hq,hr⟩

theorem selfAt {Γ : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Γ types) (more : List Ty) (i : Fin more.length) :
    argumentAt (selfArguments f base types extras more) i=.marked f (more.get i) base types extras := by
  induction more with
  | nil => exact Fin.elim0 i
  | cons τ rest ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j

theorem emptyIdentity {Γ : List Ty} {τ : Ty} (q : MarkedTerm Symbol arity Γ τ) :
    applyOriginalWith q (fun v => .var v) (.nil : Arguments Symbol arity Γ []) rfl=some q := by
  rw [ActualOriginalApplicationSupportProof.emptyEquation,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Γ τ q]
  rfl

theorem relatedWeakCurrent (above : Symbol → Symbol → Prop) {P : World I} {τ : Ty}
    (v : Value I τ P) (q : SyntaxAt I τ P) (hrel : Related I above τ P v q)
    (o : ObservationAt I τ P) (hb : readBit false v o.val=true) :
    Weak Symbol arity above (portTypes P.val++I.context) ⟨τ,q⟩ ⟨τ,observedTerm o⟩ := by
  have H := (ActualValueLogicalRelationProof.bitClause Symbol inferInstance arity I above τ P v q hrel) P (fun _ hp => hp) o
  rw [RecursiveNaturalDomainsProof.weakeningIdentity Symbol inferInstance arity I τ P v,RelatedOccurrenceMatchingProof.syntaxIdentity] at H
  exact H.1 hb

theorem selectSound : SelectStageSoundnessTargets.SelectSound := by
  intro Symbol inst arity I above dec M f τ P a base types extras o hM ha hb
  rcases τ with ⟨τ,hτ⟩
  obtain ⟨p,hp,hcase⟩ := (MarkedSelectTestProof.selectCalibration Symbol inst arity I M f P a o.val).mp hb
  obtain ⟨q,hq,hrel⟩ := selectedRelated above f P a base types extras ha p hp
  rcases p with ⟨⟨σ,hσ⟩,v⟩
  rcases hrel with ⟨q,rfl,hrel⟩
  rcases hcase with ⟨hz,hbit⟩ | ⟨s,hsout,hbit⟩
  · have hz : σ=τ := hz.trans o.property.2.2
    subst σ
    exact Weak.select f.val base types extras [] q q (observedTerm o) rfl hq (emptyIdentity q)
      (relatedWeakCurrent above v q hrel o hbit)
  · rcases s with ⟨⟨more,υ⟩,hs⟩
    have hout : υ=τ := hsout.trans o.property.2.2
    subst υ
    let suffix : Suffix σ := ⟨(more,τ),hs⟩
    have hargs : ∀ i,Related I above (more.get i) P (selfTuple M f a ⟨σ,hσ⟩ suffix i)
        (argumentAt (selfArguments f.val base types extras more) i) := by
      intro i
      rw [selfAt]
      exact hM f (FullTuplePacking.argumentTag I ⟨σ,hσ⟩ suffix i) P a base types extras ha
    have H := (ActualValueLogicalRelationProof.fullTupleClause Symbol inst arity I above σ P v q hrel)
      P (fun _ hp => hp) suffix (selfTuple M f a ⟨σ,hσ⟩ suffix) (selfArguments f.val base types extras more) hargs
    rw [RecursiveNaturalDomainsProof.weakeningIdentity Symbol inst arity I σ P v,RelatedOccurrenceMatchingProof.syntaxIdentity] at H
    have htype : σ=arrows more τ := ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration σ more τ).mp hs).2.symm
    cases happ : applyOriginalWith q (fun x => .var x) (selfArguments f.val base types extras more) htype with
    | none =>
      simp only [happ] at H
      rw [H,TypedObservationAccessProof.bottomFalse] at hbit
      cases hbit
    | some result =>
      simp only [happ] at H
      exact Weak.select f.val base types extras more q result (observedTerm o) htype hq happ
        (relatedWeakCurrent above _ result H o hbit)

end LogicLineages.OrdinalComparison.TerminationOrdering.SelectStageSoundnessProof
