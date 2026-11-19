module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainTargets
public import LogicLineages.OrdinalComparison.SourceUnaryChainSpineProof
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnaryChain

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment SourceUnaryChain
open SourceCollisionCompletion.Proof (weaken_free weaken_closure)

private theorem sameSpine {Γ} (ws : List (OrdinalVector Γ 1)) :
    scalarSpine ws = SourceUnaryChain.Proof.spine ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [scalarSpine,SourceUnaryChain.Proof.spine,ih]

private theorem spineActive {Γ} (ws : List (OrdinalVector Γ 1)) :
    ordinalHeadFree (scalarSpine ws) = false := by
  rw [sameSpine]
  exact SourceUnaryChain.Proof.spine_free ws

private theorem tailActive {Γ} (w : OrdinalVector Γ 1) (ws : List (OrdinalVector Γ 1)) :
    ordinalHeadFree (.add (ordinalExpressionRename (Renaming.weaken Γ .ground) (w 0))
      (scalarSpine ws)) = false := by
  rw [sameSpine]
  exact SourceUnaryChain.Proof.tail_free w ws

/-- Alignment is of actual selected-policy assignments, never a syntactic
or denotational property imposed as an extra requirement on a source. -/
theorem sourceVectors (p : AdmissibleSum.Policy) {Γ} (vs : List (Unary Γ)) :
    ∃ ws : List (OrdinalVector Γ 1), Assigned p vs ws := by
  induction vs with
  | nil => exact ⟨[],List.Forall₂.nil⟩
  | cons v vs ih =>
    obtain ⟨w,hw,_⟩ := actualAdmissibleAssignmentGenerated Γ (.arrow .ground .ground) p v
    obtain ⟨ws,hws⟩ := ih
    exact ⟨w::ws,List.Forall₂.cons hw hws⟩

theorem actualBody : CurrentUnaryChainTargets.ActualBody := by
  intro p Γ vs ws h
  unfold Assigned at h
  induction h with
  | nil =>
    apply congrArg some
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl
  | @cons v w vs ws hv htail ih =>
    simp only [chainBody,assignment]
    rw [SourceRenaming.Proof.assignmentNaturality Γ (.ground :: Γ) (.arrow .ground .ground)
      (Renaming.weaken Γ .ground) p v, hv, ih]
    change some (application (σ := .ground) (τ := .ground) p
      (SourceRenaming.renameVector (Renaming.weaken Γ .ground) w) (fun _ => scalarSpine ws)) = _
    apply congrArg some
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simp [application,box,boxTail,ordinalBoxPositive,ordinalVectorAt,Ty.level,
      SourceRenaming.renameVector,scalarSpine]
    all_goals first | rfl | exact ⟨rfl,rfl⟩

private theorem freeRun (p : AdmissibleSum.Policy) {Γ} (i : Nat) (t : OrdinalExpression Γ) :
    AdmissiblePartial.run p i (ordinalExpressionRename (Renaming.weaken Γ .ground) t) =
      some (ordinalFreePartialVector i (ordinalExpressionRename (Renaming.weaken Γ .ground) t)) := by
  rw [AdmissiblePartial.run.eq_def,weaken_free]
  rfl

theorem actualPartial : CurrentUnaryChainTargets.ActualPartial := by
  intro p Γ ws
  induction ws with
  | nil =>
    simp [scalarSpine,partialSpine,AdmissiblePartial.run,ordinalHeadFree,ordinalHeadOccurs,
      ordinalHeadComponentOccurs]
  | cons v ws ih =>
    rw [AdmissiblePartial.run.eq_def,spineActive]
    simp only [↓reduceIte,scalarSpine]
    rw [freeRun,AdmissiblePartial.run.eq_def,tailActive]
    simp only [↓reduceIte]
    rw [freeRun,ih]
    apply congrArg some
    funext j
    have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; simp only [Ty.level] at this; omega
    rcases hj with hj | hj <;>
      simp [partialSpine,hj,ordinalFreePartialVector,weaken_closure]
    all_goals first | rfl | exact ⟨rfl,rfl⟩

theorem finalAbstractionHead (p : AdmissibleSum.Policy) {Γ} (t : OrdinalExpression (.ground :: Γ))
    (ps : OrdinalPartialVector Γ .ground) (u : OrdinalVector Γ 1)
    (hp : AdmissiblePartial.run p 0 t = some ps)
    (hu : abstraction p (fun _ : Fin 1 => t) = some u) : u 1 = ps 1 := by
  unfold abstraction at hu
  simp only [Ty.level,collect,Fin.val_zero,hp,Option.bind_some] at hu
  have he := congrArg (fun v : OrdinalVector Γ 1 => v 1) (Option.some.inj hu)
  have hs : p.shape .positiveAbstraction 0 = .leaf :=
    PolicyGadget.smallShapes.2.1 (p.shape .positiveAbstraction 0)
  simp [hs,AdmissibleSum.expand,Fin.cases_zero,Ty.level] at he
  exact he.symm

end LogicLineages.ControlSensitivityCurrent.CurrentUnaryChain
