module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessMatchingProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess RecursiveComparison SourceConstructorIteration ActualComparisonCompleteness ActualComparisonCompletenessSupportProof FiniteOccurrenceMatching

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem orderedTruth (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    {ss ts : List (RecursiveComparison.Packed Symbol arity Γ)} (hm : List.Forall₂ (Meaning (I := I) above false) ss ts)
    (P : World I) (r : Renaming Γ (Source.SourcePortContexts.portTypes P.val++I.context))
    {vs : List (TypedExtraDownsets.Packed I P)} {os : List (Obs I)}
    (hv : List.Forall₂ (SourceMatch (limit I above) P (reindex r (identity I P))) ss vs)
    (ho : List.Forall₂ (TargetMatch P r) ts os) : List.Forall₂ (fun v o => pairBit false v o=true) vs os := by
  induction hm generalizing vs os with
  | nil => cases hv; cases ho; exact .nil
  | cons hhead htail ih =>
    cases hv with
    | cons hvh hvt =>
      cases ho with
      | cons hoh hot => exact .cons (pairTruth above false hhead P r hvh hoh) (ih hvt hot)

theorem weakTruth (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    {ss ts matched : List (RecursiveComparison.Packed Symbol arity Γ)} (hp : ts.Perm matched)
    (hm : List.Forall₂ (Meaning (I := I) above false) ss matched)
    (P : World I) (r : Renaming Γ (Source.SourcePortContexts.portTypes P.val++I.context))
    {vs : List (TypedExtraDownsets.Packed I P)} {os : List (Obs I)}
    (hv : List.Forall₂ (SourceMatch (limit I above) P (reindex r (identity I P))) ss vs)
    (ho : List.Forall₂ (TargetMatch P r) ts os) : weakTest (pairBit false) vs os=true := by
  rcases List.perm_comp_forall₂ hp.symm ho with ⟨mos,hmose,hperm⟩
  exact (FiniteOccurrenceMatchingProof.weakCalibration Symbol inferInstance arity I P vs os).mpr
    ⟨mos,hperm.symm,orderedTruth above hm P r hv hmose⟩

theorem replacementTruth (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    {removed inserted : List (RecursiveComparison.Packed Symbol arity Γ)}
    (hm : ∀ t ∈ inserted,∃ s ∈ removed,Meaning (I := I) above true s t)
    (P : World I) (r : Renaming Γ (Source.SourcePortContexts.portTypes P.val++I.context))
    {vs : List (TypedExtraDownsets.Packed I P)} {os : List (Obs I)}
    (hv : List.Forall₂ (SourceMatch (limit I above) P (reindex r (identity I P))) removed vs)
    (ho : List.Forall₂ (TargetMatch P r) inserted os) : ∀ o ∈ os,∃ v ∈ vs,pairBit true v o=true := by
  intro o hom
  rcases rightWitness ho hom with ⟨t,ht,hmatch⟩
  rcases hm t ht with ⟨s,hs,hmeaning⟩
  rcases leftWitness hv hs with ⟨v,hv,hsource⟩
  exact ⟨v,hv,pairTruth above true hmeaning P r hsource hmatch⟩

theorem strictTruth (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    {ss ts : List (RecursiveComparison.Packed Symbol arity Γ)} (hm : MultiMeaning (I := I) above ss ts)
    (P : World I) (r : Renaming Γ (Source.SourcePortContexts.portTypes P.val++I.context))
    {vs : List (TypedExtraDownsets.Packed I P)} {os : List (Obs I)}
    (hv : List.Forall₂ (SourceMatch (limit I above) P (reindex r (identity I P))) ss vs)
    (ho : List.Forall₂ (TargetMatch P r) ts os) : strictTest (pairBit false) (pairBit true) vs os=true := by
  rcases hm with ⟨kept,removed,retained,inserted,hsp,htp,hn,hw,hr⟩
  rcases List.perm_comp_forall₂ hsp.symm hv with ⟨vsplit,hvsplit,hvp⟩
  rcases List.perm_comp_forall₂ htp.symm ho with ⟨osplit,hosplit,hop⟩
  rcases splitMatch kept removed hvsplit with ⟨vk,vr,rfl,hvk,hvr⟩
  rcases splitMatch retained inserted hosplit with ⟨ot,oi,rfl,hot,hoi⟩
  have hvrn : vr≠[] := by
    intro he
    cases removed with
    | nil => exact hn rfl
    | cons a rest => have hl := hvr.length_eq; simp [he] at hl
  exact (FiniteOccurrenceMatchingProof.strictCalibration Symbol inferInstance arity I P vs os).mpr
    ⟨vk,vr,ot,oi,hvp.symm,hop.symm,hvrn,orderedTruth above hw P r hvk hot,
      replacementTruth above hr P r hvr hoi⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessMatchingProof
