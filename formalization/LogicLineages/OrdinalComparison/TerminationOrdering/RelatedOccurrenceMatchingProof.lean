module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatchingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatchingProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits RecursiveNaturalDomains TypedObservationAccess RecursiveComparison TypedExtraDownsets FiniteOccurrenceMatching ConstructorInputLogicalRelation ActualValueLogicalRelation ActualComparisonCompletenessSupportProof RelatedOccurrenceMatching

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem syntaxIdentity {τ : Ty} {P : World I} (q : SyntaxAt I τ P) : futureSyntax (fun _ hp => hp) q=q := by
  have hr : @Eq (Renaming (portTypes P.val++I.context) (portTypes P.val++I.context))
      (LogicalRelationWorlds.portRename (P := P) (Q := P) (fun _ hp => hp)) (fun {_} v => v) := by
    funext υ v
    exact LogicalRelationWorldsProof.portRenameIdentity Symbol inferInstance arity I P υ v
  exact (congrArg (fun r : Renaming (portTypes P.val++I.context) (portTypes P.val++I.context) => renameTerm q r) hr).trans
    (Source.SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity _ τ q)

theorem pairSound : RelatedOccurrenceMatchingTargets.PairSound := by
  intro Symbol inst arity I above P a o s t ha ho
  rcases ha with ⟨q,rfl,hq⟩
  rcases ho with ⟨hom,hp,rfl⟩
  have H : ∀ strict : Bool,pairBit strict a o=true →
      if strict then Strict Symbol arity above (portTypes P.val++I.context) ⟨a.1.val,q⟩ (decode o hp)
      else Weak Symbol arity above (portTypes P.val++I.context) ⟨a.1.val,q⟩ (decode o hp) := by
    intro strict hb
    obtain ⟨accepted,_⟩ := (TypedObservationAccessProof.trueCalibration Symbol inst arity I a.1.val P strict a.2 o).mp hb
    let obs : ObservationAt I a.1.val P := ⟨o,hom,hp,accepted.2.2.1⟩
    have hbits := (ActualValueLogicalRelationProof.bitClause Symbol inst arity I above a.1.val P a.2 q hq) P (fun _ hp => hp) obs
    rw [RecursiveNaturalDomainsProof.weakeningIdentity Symbol inst arity I a.1.val P a.2,syntaxIdentity] at hbits
    rw [targetTyped obs]
    cases strict with
    | false => exact hbits.1 hb
    | true => exact hbits.2 hb
  exact ⟨H false,H true⟩

theorem orderedSound (above : Symbol → Symbol → Prop) (P : World I)
    {values : List (TypedExtraDownsets.Packed I P)} {os : List (Observation Symbol arity I.context (budget I))}
    {ss ts : List (RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context))}
    (hb : List.Forall₂ (fun v o => pairBit false v o=true) values os)
    (hv : List.Forall₂ (PackedRelated I above P) values ss) (ho : List.Forall₂ (Observed I P) os ts) :
    WeakMatch Symbol arity above (portTypes P.val++I.context) ss ts := by
  induction hb generalizing ss ts with
  | nil => cases hv; cases ho; exact .nil
  | cons hh ht ih =>
    cases hv with
    | cons hvh hvt =>
      cases ho with
      | cons hoh hot => exact .cons _ _ _ _ ((pairSound Symbol inferInstance arity I above P _ _ _ _ hvh hoh).1 hh) (ih hvt hot)

theorem weakSound : RelatedOccurrenceMatchingTargets.WeakSound := by
  intro Symbol inst arity I above P values os ss ts hv ho hb
  obtain ⟨matched,hp,hm⟩ := (FiniteOccurrenceMatchingProof.weakCalibration Symbol inst arity I P values os).mp hb
  obtain ⟨targets,ht,hperm⟩ := List.perm_comp_forall₂ hp.symm ho
  exact ⟨targets,hperm.symm,orderedSound above P hm hv ht⟩

theorem replacementSound (above : Symbol → Symbol → Prop) (P : World I)
    {values : List (TypedExtraDownsets.Packed I P)} {os : List (Observation Symbol arity I.context (budget I))}
    {ss ts : List (RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context))}
    (hb : ∀ o ∈ os,∃ v ∈ values,pairBit true v o=true)
    (hv : List.Forall₂ (PackedRelated I above P) values ss) (ho : List.Forall₂ (Observed I P) os ts) :
    ReplacementMatch Symbol arity above (portTypes P.val++I.context) ss ts := by
  have H : ∀ t ∈ ts,∃ s ∈ ss,Strict Symbol arity above (portTypes P.val++I.context) s t := by
    intro t ht
    obtain ⟨o,hom,hoq⟩ := rightWitness ho ht
    obtain ⟨v,hvm,hbit⟩ := hb o hom
    obtain ⟨s,hsm,hvq⟩ := leftWitness hv hvm
    exact ⟨s,hsm,(pairSound Symbol inferInstance arity I above P v o s t hvq hoq).2 hbit⟩
  clear hb hv ho
  induction ts with
  | nil => exact .nil _
  | cons t rest ih =>
    obtain ⟨s,hs,hst⟩ := H t List.mem_cons_self
    exact .cons _ _ _ _ hs hst (ih (fun t ht => H t (List.mem_cons_of_mem _ ht)))

theorem strictSound : RelatedOccurrenceMatchingTargets.StrictSound := by
  intro Symbol inst arity I above P values os ss ts hv ho hb
  obtain ⟨kept,removed,retained,inserted,hp,hq,hn,hw,hr⟩ :=
    (FiniteOccurrenceMatchingProof.strictCalibration Symbol inst arity I P values os).mp hb
  obtain ⟨splitSource,hvs,hsp⟩ := List.perm_comp_forall₂ hp.symm hv
  obtain ⟨splitTarget,hos,htp⟩ := List.perm_comp_forall₂ hq.symm ho
  obtain ⟨sk,sr,rfl,hvk,hvr⟩ := splitMatch kept removed hvs
  obtain ⟨st,si,rfl,hot,hoi⟩ := splitMatch retained inserted hos
  have hsr : sr≠[] := by
    intro he
    have hl := hvr.length_eq
    rw [he] at hl
    have hz : removed=[] := List.length_eq_zero_iff.mp hl
    exact hn hz
  exact StrictMultiset.replace ss ts sk st sr si hsp.symm htp.symm hsr
    (orderedSound above P hw hvk hot) (replacementSound above P hr hvr hoi)

end LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatchingProof
