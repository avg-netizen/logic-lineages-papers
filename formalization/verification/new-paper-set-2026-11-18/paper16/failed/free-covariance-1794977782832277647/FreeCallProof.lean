import LogicLineages.PersistentMarking.FreeCompositionProof
import LogicLineages.PersistentMarking.SpineShiftProof

namespace LogicLineages.PersistentMarking.FreeCallProof
open Spine

theorem annotation (θ : FreeMap) (ht : ∀ σ x, (θ σ x).type = σ)
    (d : Nat) (q : Expr) : (freeSub θ d q).type = q.type := by
  cases q with
  | free σ x => simp only [freeSub, SubstitutionProof.shiftType, ht, Expr.type]
  | bound σ i => rfl
  | lam σ body => simp only [freeSub, Expr.type, annotation θ ht (d+1) body]
  | head f base => rfl
  | marked f τ base extras => rfl
termination_by sizeOf q

theorem consume (θ : FreeMap) (ht : ∀ σ x, (θ σ x).type = σ)
    (σ : Ty) (args : Args) : consumeTypes σ (freeSubArgs θ 0 args) = consumeTypes σ args := by
  cases args with
  | nil => simp [freeSubArgs, consumeTypes]
  | cons a rest =>
    cases σ with
    | ground => simp [freeSubArgs, consumeTypes]
    | arrow δ τ => simp only [freeSubArgs, consumeTypes, annotation θ ht, consume θ ht τ rest]
termination_by sizeOf args

theorem aux (θ : FreeMap) (ht : ∀ σ x, (θ σ x).type = σ)
    (q : Expr) (args values : Args) (r : Expr)
    (hr : applyAux q args values = some r) :
    applyAux (freeSub θ values.length q) (freeSubArgs θ 0 args)
      (freeSubArgs θ 0 values) = some (freeSub θ 0 r) := by
  cases args with
  | nil =>
    simp only [applyAux, Option.some.injEq] at hr
    subst r
    simp only [freeSubArgs, applyAux]
    exact congrArg some (by simpa only [Nat.zero_add] using
      (FreeCompositionProof.composition θ values 0 q).symm)
  | cons a rest =>
    cases q with
    | free σ x => simp [applyAux] at hr
    | bound σ i => simp [applyAux] at hr
    | lam σ body =>
      by_cases ha : a.type = σ
      · have hs : applyAux body rest (.cons a values) = some r := by simpa [applyAux, ha] using hr
        have ih := aux θ ht body rest (.cons a values) r hs
        simpa [freeSub, freeSubArgs, applyAux, annotation θ ht, ha, Args.length, Nat.add_comm 1] using ih
      · simp [applyAux, ha] at hr
    | head f base =>
      cases hc : consumeTypes f.result (.cons a rest) with
      | none => simp [applyAux, hc] at hr
      | some τ =>
        simp only [applyAux, hc, Option.map_some, Option.some.injEq] at hr
        subst r
        simp only [freeSub, freeSubArgs, applyAux]
        rw [show consumeTypes f.result (.cons (freeSub θ 0 a) (freeSubArgs θ 0 rest)) = some τ from
          (consume θ ht f.result (.cons a rest)).trans hc]
        simp only [Option.map_some]
        exact congrArg some (congrArg (fun bs => Expr.marked f τ bs (.cons (freeSub θ 0 a) (freeSubArgs θ 0 rest)))
          (by simpa only [Nat.zero_add] using (FreeCompositionProof.compositionArgs θ values 0 base).symm))
    | marked f σ base extras =>
      cases hc : consumeTypes σ (.cons a rest) with
      | none => simp [applyAux, hc] at hr
      | some τ =>
        simp only [applyAux, hc, Option.map_some, Option.some.injEq] at hr
        subst r
        simp only [freeSub, freeSubArgs, applyAux]
        rw [show consumeTypes σ (.cons (freeSub θ 0 a) (freeSubArgs θ 0 rest)) = some τ from
          (consume θ ht σ (.cons a rest)).trans hc]
        simp only [Option.map_some]
        rw [FreeCompositionProof.mapAppend]
        rw [FreeCompositionProof.compositionArgs θ values 0 base,
          FreeCompositionProof.compositionArgs θ values 0 extras]
        rfl
termination_by sizeOf args

theorem annotationPreserves : FreeCovarianceTargets.AnnotationPreserves := by
  intro Γ θ ht d q
  exact annotation θ (fun σ x => SpineShiftProof.annotationExact Γ (θ σ x) σ (ht σ x)) d q

theorem successfulCallCovariance : FreeCovarianceTargets.SuccessfulCallCovariance := by
  intro Γ θ q σ args τ r ht _ _ hr
  have hθ : ∀ δ x, (θ δ x).type = δ :=
    fun δ x => SpineShiftProof.annotationExact Γ (θ δ x) δ (ht δ x)
  cases args with
  | nil =>
    simp only [apply, Option.some.injEq] at hr
    subst r
    rfl
  | cons a rest =>
    exact aux θ hθ q (.cons a rest) .nil r hr
end LogicLineages.PersistentMarking.FreeCallProof
