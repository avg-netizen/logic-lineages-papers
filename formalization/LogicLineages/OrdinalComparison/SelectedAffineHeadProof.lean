module
public import LogicLineages.OrdinalComparison.SelectedAffineHeadTargets
public import LogicLineages.OrdinalComparison.SelectedHeadCarrierProof
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedAffineHead.Proof
open ActiveScalarAnnotation AdditiveHeadTree HeadFiniteSurplus OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem exactSelectionCoverage : Targets.ExactSelectionCoverage := by
  intro k Γ F q h
  constructor
  · intro hs
    induction hs with
    | here ha => exact ⟨_,.here ha⟩
    | addLeft hs ih => obtain ⟨t,ht⟩ := ih; exact ⟨t,.addLeft ht⟩
    | addRight hs ih => obtain ⟨t,ht⟩ := ih; exact ⟨t,.addRight ht⟩
    | tail hs ih => obtain ⟨t,ht⟩ := ih; exact ⟨t,.tail ht⟩
  · rintro ⟨t,hs⟩
    induction hs with
    | here ha => exact .here ha
    | addLeft hs ih => exact .addLeft ih
    | addRight hs ih => exact .addRight ih
    | tail hs ih => exact .tail ih

theorem selected_active {k Γ} (F : Variable Γ (Ty.curriedGround (k+1)))
    {q h t : OrdinalExpression Γ} (hs : SelectedCollapse F q h t) : Active F q :=
  SelectedHeadCarrier.Proof.selectedActivity k Γ F q h
    ((exactSelectionCoverage k Γ F q h).mpr ⟨t,hs⟩)

theorem selected_tree {k Γ} (F : Variable Γ (Ty.curriedGround (k+1)))
    {q h t : OrdinalExpression Γ} (hq : ScalarTrees F q)
    (hs : SelectedCollapse F q h t) : HeadTree F h := by
  induction hq generalizing h t with
  | free grade inactive => exact False.elim (inactive (selected_active F hs))
  | tracked => cases hs
  | add ha hb iha ihb =>
    cases hs with
    | addLeft hs => exact iha hs
    | addRight hs => exact ihb hs
  | collapse hh ht ih =>
    cases hs with
    | here _ => exact hh
    | tail hs => exact ih hs

theorem selected_support {k Γ} (p : AdmissibleSum.Policy)
    (F : Variable Γ (Ty.curriedGround (k+1))) {q h t : OrdinalExpression Γ}
    (hq : Annotated p F q) (hs : SelectedCollapse F q h t) : Active F h → Active F t := by
  induction hq generalizing h t with
  | free inactive => exact False.elim (inactive (selected_active F hs))
  | tracked => cases hs
  | add ha hb iha ihb =>
    cases hs with
    | addLeft hs => exact iha hs
    | addRight hs => exact ihb hs
  | collapse op support ht ih =>
    cases hs with
    | here _ => exact support
    | tail hs => exact ih hs

theorem selectedTreeSupport : Targets.SelectedTreeSupport := by
  intro k Γ F p q h t ht ha hs
  exact ⟨selected_tree F ht hs,selected_support p F ha hs⟩

theorem head_conclusion {k Γ} (p : AdmissibleSum.Policy)
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ht : HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h) :
    HeadConclusion p h := by
  obtain ⟨v,hv,he⟩ := HeadFiniteSurplus.Proof.exactHeadPartial k Γ p h ht
  have hb := HeadFiniteSurplus.Proof.surplusBounds k Γ h ht
  have hgrade := AdditiveHeadTree.Proof.head_grade ht
  obtain ⟨w,hw,hg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ
    (Ty.curriedGround (k+1)) p 1 h hgrade
  have hwv : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  refine ⟨ht,v,hv,hb.1,hb.2.1,?_⟩
  intro ρ μ
  have hv1 := UnaryCarrier.Proof.positive_unit_value 1 (v (outputOne k))
    (by decide) (by exact hg (outputOne k)) μ
  have hv2 := UnaryCarrier.Proof.positive_unit_value 2 (v (outputTwo k))
    (by decide) (by exact hg (outputTwo k)) μ
  have hh : denote (fun _ => 1) (ordinalHeadClosure h) =
      expressionValue (UnitObservation.substitution ρ) h :=
    (HeadFiniteSurplus.Proof.headClosure_units _).trans
      (UnaryCarrier.Proof.positive_unit_value 1 _ (by decide) hgrade ρ).symm
  refine ⟨?_,?_,?_⟩
  · calc
      expressionValue (UnitObservation.substitution μ) (v (outputOne k)) =
          denote (fun _ => 1) (v (outputOne k)) := hv1
      _ = denote (fun _ => 1) (ordinalHeadClosure h) + (surplus h : Ordinal) := (he _).1
      _ = _ := congrArg (fun x => x + (surplus h : Ordinal)) hh
  · exact hv2.trans (he _).2
  · intro hn
    apply hb.2.2 (fun _ => 1)
    rw [hh]
    exact hn

theorem completeSourceAffineHeads : Targets.CompleteSourceAffineHeads := by
  intro k Γ n p e
  obtain ⟨u,hu,hscalar,hpositive⟩ := AdditiveHeadTree.Proof.actualSourceTrees k
    (Ty.curriedGround (k+1) :: Γ) .here n p e
  obtain ⟨u',hu',hannotation⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k
    (Ty.curriedGround (k+1) :: Γ) .here n p e
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  refine ⟨u,hu,?_,?_⟩
  · intro j hj
    exact head_conclusion p _ (hpositive j hj)
  · intro h t hs
    have hc := selectedTreeSupport k _ .here p (u 0) h t hscalar hannotation hs
    exact ⟨head_conclusion p h hc.1,hc.2⟩
end LogicLineages.OrdinalComparison.Source.SelectedAffineHead.Proof
