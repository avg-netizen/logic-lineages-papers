module
public import LogicLineages.OrdinalComparison.SourceUnaryChainTargets
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionEraserProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceUnaryChain.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment
open SourceCollisionCompletion.Proof (weaken_free weaken_closure)

def spine {Γ} : List (OrdinalVector Γ 1) → OrdinalExpression (.ground :: Γ)
  | [] => .var ⟨.ground, .here, 0⟩
  | v :: ws => .collapse (ordinalExpressionRename (Renaming.weaken Γ .ground) (v 1))
      (.add (ordinalExpressionRename (Renaming.weaken Γ .ground) (v 0)) (spine ws))

def partialSpine {Γ} : List (OrdinalVector Γ 1) → OrdinalPartialVector Γ .ground
  | [] => fun _ => .one
  | v :: ws => fun j => if j.val = 0 then
      .collapse (v 1) (.add (.add (.add (v 0) .one) (partialSpine ws 0)) .one)
    else .add (.add (v 1) .one) (.add (.add .one (partialSpine ws j)) .one)

theorem weaken_occurs {Γ σ} (t : OrdinalExpression Γ) :
    ordinalHeadOccurs (ordinalExpressionRename (Renaming.weaken Γ σ) t) = false := by
  cases h : ordinalHeadOccurs (ordinalExpressionRename (Renaming.weaken Γ σ) t) with
  | false => rfl
  | true =>
    have hf : False := by simpa [ordinalHeadFree, h] using weaken_free (σ := σ) t
    exact False.elim hf

theorem spine_occurs {Γ} (ws : List (OrdinalVector Γ 1)) : ordinalHeadOccurs (spine ws) = true := by
  induction ws with
  | nil => rfl
  | cons v ws ih => simp only [spine, ordinalHeadOccurs, weaken_occurs, ih, Bool.false_or]

theorem spine_free {Γ} (ws : List (OrdinalVector Γ 1)) : ordinalHeadFree (spine ws) = false := by
  simp only [ordinalHeadFree, spine_occurs, Bool.not_true]

theorem tail_free {Γ} (v : OrdinalVector Γ 1) (ws : List (OrdinalVector Γ 1)) :
    ordinalHeadFree (.add (ordinalExpressionRename (Renaming.weaken Γ .ground) (v 0)) (spine ws)) = false := by
  simp only [ordinalHeadFree, ordinalHeadOccurs, weaken_occurs, spine_occurs, Bool.false_or, Bool.not_true]

theorem free_run {Γ} (i : Nat) (t : OrdinalExpression Γ) :
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy i
      (ordinalExpressionRename (Renaming.weaken Γ .ground) t) =
      some (ordinalFreePartialVector i (ordinalExpressionRename (Renaming.weaken Γ .ground) t)) := by
  rw [AdmissiblePartial.run.eq_def, weaken_free]
  rfl

theorem run_spine {Γ} (ws : List (OrdinalVector Γ 1)) :
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (spine ws) = some (partialSpine ws) := by
  induction ws with
  | nil =>
    simp [spine, partialSpine, AdmissiblePartial.run, ordinalHeadFree, ordinalHeadOccurs,
      ordinalHeadComponentOccurs]
  | cons v ws ih =>
    rw [AdmissiblePartial.run.eq_def, spine_free]
    simp only [↓reduceIte, spine]
    rw [free_run, AdmissiblePartial.run.eq_def, tail_free]
    simp only [↓reduceIte]
    rw [free_run, ih]
    apply congrArg some
    funext j
    have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; simp only [Ty.level] at this; omega
    rcases hj with hj | hj <;>
      simp [partialSpine, hj, ordinalFreePartialVector, weaken_closure, AdmissiblePartial.three,
        OrdinalSyntax.defaultPolicy, OrdinalSyntax.defaultShape, OrdinalSyntax.leftShape,
        AdmissibleSum.expand]
    all_goals first | rfl | exact ⟨rfl, rfl⟩

theorem source_vectors {Γ} (vs : List (OriginalTerm Γ (.arrow .ground .ground))) :
    ∃ ws : List (OrdinalVector Γ 1),
      List.Forall₂ (fun v w => assignment OrdinalSyntax.defaultPolicy v = some w) vs ws := by
  induction vs with
  | nil => exact ⟨[], .nil⟩
  | cons v vs ih =>
    obtain ⟨w, hw, _⟩ := actualAdmissibleAssignmentGenerated Γ (.arrow .ground .ground) OrdinalSyntax.defaultPolicy v
    obtain ⟨ws, hws⟩ := ih
    exact ⟨w :: ws, .cons hw hws⟩

theorem body_assignment {Γ} (vs : List (OriginalTerm Γ (.arrow .ground .ground)))
    (ws : List (OrdinalVector Γ 1))
    (h : List.Forall₂ (fun v w => assignment OrdinalSyntax.defaultPolicy v = some w) vs ws) :
    assignment OrdinalSyntax.defaultPolicy (chainBody vs) = some (fun _ => spine ws) := by
  induction h with
  | nil =>
    apply congrArg some
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl
  | @cons v w vs ws hv htail ih =>
    simp only [chainBody, assignment]
    rw [SourceRenaming.Proof.assignmentNaturality Γ (.ground :: Γ) (.arrow .ground .ground)
      (Renaming.weaken Γ .ground) OrdinalSyntax.defaultPolicy v, hv, ih]
    change some (application (σ := .ground) (τ := .ground) OrdinalSyntax.defaultPolicy
      (SourceRenaming.renameVector (Renaming.weaken Γ .ground) w) (fun _ => spine ws)) = _
    apply congrArg some
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simp [application, box, boxTail, ordinalBoxPositive, ordinalVectorAt, Ty.level,
      SourceRenaming.renameVector, spine]
    all_goals first | rfl | exact ⟨rfl, rfl⟩

theorem abstraction_head {Γ} (t : OrdinalExpression (.ground :: Γ))
    (ps : OrdinalPartialVector Γ .ground) (u : OrdinalVector Γ 1)
    (hp : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 t = some ps)
    (hu : abstraction OrdinalSyntax.defaultPolicy (fun _ : Fin 1 => t) = some u) : u 1 = ps 1 := by
  unfold abstraction at hu
  simp only [Ty.level, collect, Fin.val_zero, hp, Option.bind_some] at hu
  have he := congrArg (fun v : OrdinalVector Γ 1 => v 1) (Option.some.inj hu)
  simp [OrdinalSyntax.defaultPolicy, OrdinalSyntax.defaultShape, OrdinalSyntax.leftShape,
    AdmissibleSum.expand, Fin.cases_zero, Ty.level] at he
  exact he.symm
end LogicLineages.OrdinalComparison.Source.SourceUnaryChain.Proof
