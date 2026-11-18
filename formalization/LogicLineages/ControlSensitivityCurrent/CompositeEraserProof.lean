module
public import LogicLineages.ControlSensitivityCurrent.CompositeEraserTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetProof
public import LogicLineages.OrdinalComparison.ParametricSourceEraserClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CompositeEraser
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment
open SourceCollisionCompletion (eraser)
open SourceCollisionCompletion.Proof (inflated unusedVector eraserVector weaken_free weaken_closure)
private theorem shape0 (p : AdmissibleSum.Policy) (site : AdmissibleSum.MacroSite) :
    p.shape site 0 = .leaf := PolicyGadget.smallShapes.2.1 _
private theorem shape1 (p : AdmissibleSum.Policy) (site : AdmissibleSum.MacroSite) :
    p.shape site 1 = .join .leaf .leaf := PolicyGadget.smallShapes.2.2 _
private theorem unused_abstraction (policy : AdmissibleSum.Policy) {Γ} (v : OrdinalVector Γ 0) :
    abstraction policy
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
  have hp : AdmissiblePartial.run policy 0
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
    simp [hj, unusedVector, inflated, repeated, shape0, shape1, AdmissibleSum.expand,
      Fin.cases_zero, weaken_closure]

private theorem eraser_assignment (policy : AdmissibleSum.Policy) {Γ} (p q : OriginalTerm Γ .ground)
    (vp vq : OrdinalVector Γ 0)
    (hp : assignment policy p = some vp)
    (hq : assignment policy q = some vq) :
    assignment policy (eraser p q) = some (eraserVector (vp 0) (vq 0)) := by
  simp only [eraser, assignment]
  rw [SourceRenaming.Proof.assignmentNaturality Γ (.ground :: Γ) .ground
    (Renaming.weaken Γ .ground) policy p, hp, hq]
  change (abstraction policy
    (SourceRenaming.renameVector (Renaming.weaken Γ .ground) vp)).bind
    (fun f => some (application (σ := .ground) (τ := .ground) policy f vq)) = _
  rw [unused_abstraction policy]
  change some (application (σ := .ground) (τ := .ground) policy
    (unusedVector (vp 0)) vq) = _
  apply congrArg some
  funext j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  simp [application, box, boxTail, ordinalBoxPositive, ordinalVectorAt, Ty.level,
    unusedVector, eraserVector]
  rfl

theorem assignmentClosure : CompositeEraserTargets.AssignmentClosure := by
  intro policy Γ a b va vb ha hb
  exact eraser_assignment policy a b va vb ha hb

theorem scalarUniqueness : CompositeEraserTargets.ScalarUniqueness := by
  intro p f Γ ν t x y hx hy
  obtain ⟨vx,hvx,hex⟩ := hx
  obtain ⟨vy,hvy,hey⟩ := hy
  cases Option.some.inj (hvx.symm.trans hvy)
  exact Nat.cast_injective (hex.symm.trans hey)

theorem finiteClosure : CompositeEraserTargets.FiniteClosure := by
  intro p f hm hi Γ ν a b x y ha hb
  obtain ⟨va,hva,hea⟩ := ha
  obtain ⟨vb,hvb,heb⟩ := hb
  have hr : Scalar p f ν (eraser a b) (f (3*x+y+4)+1) :=
    ⟨_,assignmentClosure p Γ a b va vb hva hvb,
      ParametricSourceEraser.Proof.eraser_value f hm hi ν (va 0) (vb 0) x y hea heb⟩
  refine ⟨hr,?_⟩
  intro z
  constructor
  · intro hz
    exact scalarUniqueness p f Γ ν _ _ _ hz hr
  · rintro rfl
    exact hr
#audit_namespace LogicLineages.ControlSensitivityCurrent.CompositeEraser
end LogicLineages.ControlSensitivityCurrent.CompositeEraser
