module
public import LogicLineages.OrdinalComparison.GroundCarrierTransportAccountingProof
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingProof
public import LogicLineages.OrdinalComparison.WWGroundClosingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.Proof
open ScalarCarrierAccounting OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem groundMap_grade {Γ Δ : List Ty} (r : GroundClosing.GroundMap Γ Δ)
    (i : Nat) (q : OrdinalExpression Γ) (hg : GeneratedOrdinalGrade Γ i q) :
    GeneratedOrdinalGrade Δ i (GroundClosing.expression r q) := by
  induction hg with
  | one i => exact .one i
  | omega i hi => exact .omega i hi
  | @var σ x j =>
    cases hr : r x with
    | var y =>
      simpa only [GroundClosing.expression,substitute,GroundClosing.component,hr] using
        GeneratedOrdinalGrade.var y j
    | zero =>
      simpa only [GroundClosing.expression,substitute,GroundClosing.component,hr] using
        GeneratedOrdinalGrade.one (Γ := Δ) j.val
  | add ha hb iha ihb => exact .add iha ihb
  | emul hi ha hb iha ihb => exact .emul hi iha ihb
  | collapse ha hb iha ihb => exact .collapse iha ihb

theorem actualSourceGroundTransport : Targets.ActualSourceGroundTransport := by
  intro k Γ Δ n r e
  obtain ⟨u,xs,c,v,hu,haccount,hv,hvalue⟩ := ScalarCarrierAccounting.Proof.actualSourceAccounting k Γ n e
  let w := GroundClosing.partialVector r v
  have hclosed : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
      (close r (TrackedSource.erase e)) = some (GroundClosing.vector r.lift u) := by
    rw [close,GroundClosing.Proof.assignmentNaturality,hu]
    rfl
  have hw : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0
      (GroundClosing.expression r.lift (u 0)) = some w := by
    rw [GroundClosing.Proof.partialNaturality,hv]
    rfl
  obtain ⟨u',hu',hgu⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated
    (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n) OrdinalSyntax.defaultPolicy (TrackedSource.erase e)
  have heu : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  obtain ⟨v',hv',hgv⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ
    (Ty.curriedGround (k+1)) OrdinalSyntax.defaultPolicy 0 (u 0) (hgu 0)
  have hev : v' = v := Option.some.inj (hv'.symm.trans hv)
  subst v'
  have hvg : GeneratedOrdinalGrade Γ 1 (v (HeadFiniteSurplus.outputOne k)) :=
    hgv (HeadFiniteSurplus.outputOne k)
  have hwg : GeneratedOrdinalGrade Δ 1 (w (HeadFiniteSurplus.outputOne k)) :=
    groundMap_grade r 1 _ hvg
  have hold : unitValue (v (HeadFiniteSurplus.outputOne k)) = carrierSum xs + (c : Ordinal) :=
    (UnaryCarrier.Proof.positive_unit_value 1 _ (by decide) hvg (fun _ => 0)).symm.trans (hvalue (fun _ => 0))
  refine ⟨u,xs,c,v,w,hu,haccount,hv,hclosed,
    exactAccountTransport k Γ Δ r (u 0) xs c haccount,hw,rfl,?_⟩
  intro μ
  calc
    expressionValue (UnitObservation.substitution μ) (w (HeadFiniteSurplus.outputOne k)) =
        unitValue (w (HeadFiniteSurplus.outputOne k)) :=
      UnaryCarrier.Proof.positive_unit_value 1 _ (by decide) hwg μ
    _ = unitValue (v (HeadFiniteSurplus.outputOne k)) :=
      exactUnitValue Γ Δ r (v (HeadFiniteSurplus.outputOne k))
    _ = carrierSum xs + (c : Ordinal) := hold
end LogicLineages.OrdinalComparison.Source.GroundCarrierTransport.Proof
