module
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusPartialProof
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeProof
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Proof
open OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem headClosure_units {Γ : List Ty} {σ : Ty} (t : OrdinalExpression (σ :: Γ)) :
    denote (fun _ => 1) (ordinalHeadClosure t) = denote (fun _ => 1) t := by
  induction t with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x <;> rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [ordinalHeadClosure,substitute,denote] at iha ihb ⊢
    rw [iha,ihb]

theorem actualSourceSurplus : Targets.ActualSourceSurplus := by
  intro k Γ r p e
  obtain ⟨u,hu,hscalar,hheads⟩ := AdditiveHeadTree.Proof.actualSourceTrees k
    (Ty.curriedGround (k+1) :: Γ) .here (r+1) p e
  have ht := hheads (UnaryCarrier.headIndex r) (by change 0 < 1; decide)
  obtain ⟨v,hv,he⟩ := exactHeadPartial k Γ p (u (UnaryCarrier.headIndex r)) ht
  have hb := surplusBounds k Γ (u (UnaryCarrier.headIndex r)) ht
  have hgrade := AdditiveHeadTree.Proof.head_grade ht
  obtain ⟨w,hw,hg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ
    (Ty.curriedGround (k+1)) p 1 (u (UnaryCarrier.headIndex r)) hgrade
  have hwv : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  refine ⟨u,v,hu,hv,hb.1,hb.2.1,?_⟩
  intro ρ μ
  have hv1 := UnaryCarrier.Proof.positive_unit_value 1 (v (outputOne k))
    (by decide) (by exact hg (outputOne k)) μ
  have hv2 := UnaryCarrier.Proof.positive_unit_value 2 (v (outputTwo k))
    (by decide) (by exact hg (outputTwo k)) μ
  have hh : denote (fun _ => 1) (ordinalHeadClosure (u (UnaryCarrier.headIndex r))) =
      expressionValue (UnitObservation.substitution ρ) (u (UnaryCarrier.headIndex r)) :=
    (headClosure_units _).trans
      (UnaryCarrier.Proof.positive_unit_value 1 _ (by decide) hgrade ρ).symm
  refine ⟨?_,?_,?_⟩
  · calc
      expressionValue (UnitObservation.substitution μ) (v (outputOne k)) =
          denote (fun _ => 1) (v (outputOne k)) := hv1
      _ = denote (fun _ => 1) (ordinalHeadClosure (u (UnaryCarrier.headIndex r))) +
          (surplus (u (UnaryCarrier.headIndex r)) : Ordinal) := (he _).1
      _ = _ := congrArg (fun x => x + (surplus (u (UnaryCarrier.headIndex r)) : Ordinal)) hh
  · exact hv2.trans (he _).2
  · intro hn
    apply hb.2.2 (fun _ => 1)
    rw [hh]
    exact hn
end LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Proof
