module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionTargets
public import LogicLineages.OrdinalComparison.WWSourceRenamingProof
public import LogicLineages.OrdinalComparison.WWTypedComponentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment

def inflated {Γ} (t : OrdinalExpression Γ) : OrdinalExpression Γ :=
  .add (.add (.add t .one) (.add t .one)) t

def unusedVector {Γ} (t : OrdinalExpression Γ) : OrdinalVector Γ 1 :=
  fun j => if j.val = 0 then inflated t else .one

def eraserVector {Γ} (a b : OrdinalExpression Γ) : OrdinalVector Γ 0 :=
  fun _ => .collapse .one (.add (inflated a) b)

theorem weaken_free {Γ σ} (t : OrdinalExpression Γ) :
    ordinalHeadFree (ordinalExpressionRename (Renaming.weaken Γ σ) t) = true := by
  have ho : ordinalHeadOccurs (ordinalExpressionRename (Renaming.weaken Γ σ) t) = false := by
    induction t with
    | var c => rcases c with ⟨τ, x, j⟩; rfl
    | zero | one | omega => rfl
    | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
      simp only [ordinalExpressionRename, substitute, ordinalHeadOccurs] at *
      rw [ihf, ihg]
      rfl
  simp only [ordinalHeadFree, ho, Bool.not_false]

theorem weaken_closure {Γ σ} (t : OrdinalExpression Γ) :
    ordinalHeadClosure (ordinalExpressionRename (Renaming.weaken Γ σ) t) = t :=
  actualTypedOrdinalHeadClosure.2 Γ σ t

theorem unused_abstraction {Γ} (v : OrdinalVector Γ 0) :
    abstraction OrdinalSyntax.defaultPolicy
      (SourceRenaming.renameVector (Renaming.weaken Γ .ground) v) = some (unusedVector (v 0)) := by
  let t := v 0
  have hv : v = (fun _ => t) := by
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl
  have hf := weaken_free (σ := Ty.ground) t
  have hs : ordinalPartialSize (ordinalExpressionRename (Renaming.weaken Γ .ground) t) = 1 := by
    rw [ordinalPartialSize.eq_def, hf]
    rfl
  have hp : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0
      (ordinalExpressionRename (Renaming.weaken Γ .ground) t) =
      some (fun j : Fin 2 => if j.val = 0 then .add t .one else .one) := by
    rw [AdmissiblePartial.run.eq_def, hf]
    simp only [↓reduceIte]
    apply congrArg some
    funext j
    simp only [ordinalFreePartialVector, weaken_closure]
    simp [eq_comm]
    rfl
  rw [hv]
  simp only [abstraction, SourceRenaming.renameVector, Ty.level,
    List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hs, collect, Fin.val_zero, hp, Option.bind_some]
  apply congrArg some
  funext j
  have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
  rcases hj with hj | hj <;>
    simp [hj, unusedVector, inflated, repeated, OrdinalSyntax.defaultPolicy,
      OrdinalSyntax.defaultShape, OrdinalSyntax.leftShape, AdmissibleSum.expand,
      Fin.cases_zero, weaken_closure]

theorem eraser_assignment {Γ} (p q : OriginalTerm Γ .ground)
    (vp vq : OrdinalVector Γ 0)
    (hp : assignment OrdinalSyntax.defaultPolicy p = some vp)
    (hq : assignment OrdinalSyntax.defaultPolicy q = some vq) :
    assignment OrdinalSyntax.defaultPolicy (eraser p q) = some (eraserVector (vp 0) (vq 0)) := by
  simp only [eraser, assignment]
  rw [SourceRenaming.Proof.assignmentNaturality Γ (.ground :: Γ) .ground
    (Renaming.weaken Γ .ground) OrdinalSyntax.defaultPolicy p, hp, hq]
  change (abstraction OrdinalSyntax.defaultPolicy
    (SourceRenaming.renameVector (Renaming.weaken Γ .ground) vp)).bind
    (fun f => some (application (σ := .ground) (τ := .ground) OrdinalSyntax.defaultPolicy f vq)) = _
  rw [unused_abstraction]
  change some (application (σ := .ground) (τ := .ground) OrdinalSyntax.defaultPolicy
    (unusedVector (vp 0)) vq) = _
  apply congrArg some
  funext j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  simp [application, box, boxTail, ordinalBoxPositive, ordinalVectorAt, Ty.level,
    unusedVector, eraserVector]
  rfl
end LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
