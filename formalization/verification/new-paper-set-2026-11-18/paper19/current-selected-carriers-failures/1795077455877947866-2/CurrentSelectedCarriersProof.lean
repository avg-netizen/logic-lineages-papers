module
public import LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersSyntaxProof
public import LogicLineages.OrdinalComparison.SelectedHeadCarrierProof
public import LogicLineages.OrdinalComparison.TrackedSourceProof
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDenotationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriers

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment ParametricSourceSuccessor
open CurrentUnaryChain (commonUnits)

private theorem valueOnSupport (f : Nat → Nat) {Γ : List Ty} (e : OrdinalExpression Γ)
    (ν μ : OrdinalComponent Γ → Ordinal)
    (h : ∀ c ∈ ordinalExpressionVariables e, ν c = μ c) :
    denoteWith f ν e = denoteWith f μ e := by
  induction e with
  | var c => exact h c (by simp [ordinalExpressionVariables])
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [denoteWith]
    rw [iha (fun c hc => h c (List.mem_append_left _ hc)),
      ihb (fun c hc => h c (List.mem_append_right _ hc))]

private theorem positiveUnit (f : Nat → Nat) {Γ : List Ty} (i : Nat) (e : OrdinalExpression Γ)
    (hi : 0 < i) (hg : GeneratedOrdinalGrade Γ i e) (ρ : Variable Γ .ground → Nat) :
    denoteWith f (commonUnits ρ) e = denoteWith f (fun _ => 1) e := by
  apply valueOnSupport
  intro c hc
  have h := actualGeneratedComponentIndex Γ i e hg c hc
  rcases c with ⟨σ,x,j⟩
  cases σ with
  | ground =>
    change i ≤ j.val at h
    have hlt : j.val < 1 := j.isLt
    omega
  | arrow a b => rfl

private theorem groundClosedUnit (f : Nat → Nat) {Γ : List Ty} (e : OrdinalExpression Γ)
    (μ : Variable Γ .ground → Nat) :
    denoteWith f (commonUnits μ) (GroundClosing.expression (UnaryCarrier.groundMap Γ) e) =
      denoteWith f (fun _ => 1) e := by
  induction e with
  | var c =>
    rcases c with ⟨σ,x,j⟩
    cases σ <;> rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [GroundClosing.expression,substitute,denoteWith] at *
    rw [iha,ihb]

theorem groundIndependence : CurrentSelectedCarriersTargets.GroundIndependence := by
  intro f Γ i e hi hg ρ μ
  exact (groundClosedUnit f e μ).trans (positiveUnit f i e hi hg ρ).symm

private theorem renameAtUnits (f : Nat → Nat) {Γ Δ : List Ty} (r : Renaming Γ Δ)
    (e : OrdinalExpression Γ) :
    denoteWith f (fun _ => 1) (ordinalExpressionRename r e) =
      denoteWith f (fun _ => 1) e :=
  ParametricSourceSuccessor.Proof.exactSubstitution _ _ f (fun _ => 1)
    (fun c => .var (ordinalComponentRename r c)) e

theorem actualOperators : CurrentSelectedCarriersTargets.ActualOperators := by
  intro p f Γ k r F t
  obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround (r+1)) p t
  let ur := SourceRenaming.renameVector (renameTrackedAt F) u
  have hur : assignment p (t.rename (renameTrackedAt F)) = some ur := by
    rw [SourceRenaming.Proof.assignmentNaturality,hu] <;> rfl
  obtain ⟨w,hw,he⟩ := groundSaturation p _ r (t.rename (renameTrackedAt F)) ur hur
  let v := GroundClosing.vector (UnaryCarrier.groundMap _) w
  have hv : assignment p (carrierAt F r t) = some v := by
    rw [carrierAt,UnaryCarrier.closeGround,GroundClosing.StatementChecks.assignmentNaturality,hw] <;> rfl
  refine ⟨u,w,v,hu,hw,hv,rfl,rfl,carrierNoGround F r t,carrierNoOld F r t,?_⟩
  intro ρ μ
  change denoteWith f (commonUnits μ) (GroundClosing.expression (UnaryCarrier.groundMap _) (w 1)) = _
  rw [groundClosedUnit,he]
  change denoteWith f (fun _ => 1) (ordinalExpressionRename (renameTrackedAt F) (u (UnaryCarrier.headIndex r))) = _
  rw [renameAtUnits]
  exact (positiveUnit f 1 (u (UnaryCarrier.headIndex r)) (by decide) (hg (UnaryCarrier.headIndex r)) ρ).symm

theorem everySelectedHead : CurrentSelectedCarriersTargets.EverySelectedHead := by
  intro p f k Γ F n t ht
  obtain ⟨e,he⟩ := (TrackedSource.Proof.exactGrammar k Γ F n t).mp ht
  obtain ⟨v,hv,hanno⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k Γ F n p e
  rw [he] at hv
  refine ⟨v,hv,?_⟩
  intro h hs
  obtain ⟨r,op,u,hu,hh⟩ := SelectedHeadCarrier.Proof.operatorExtraction k Γ F p (v 0) h hanno hs
  obtain ⟨u',w,v',hc⟩ := actualOperators p f Γ k r F op
  have same : u' = u := Option.some.inj (hc.1.symm.trans hu)
  subst u'
  exact ⟨r,op,u,w,v',hc,hh⟩

end LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriers
