module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source

def selectGround : {Γ : List Ty} → Variable Γ .ground → Variable (groundCtx Γ) .ground
  | [],x => nomatch x
  | .ground :: _,.here => .here
  | .ground :: _,.there x => .there (selectGround x)
  | .arrow _ _ :: _,.there x => selectGround x

theorem projectOld (Γ : List Ty) (x : Variable Γ .ground) : oldGround (selectGround x) = x := by
  induction Γ with
  | nil => exact nomatch x
  | cons σ Γ ih =>
    cases σ with
    | ground =>
      cases x with
      | here => rfl
      | there x => exact congrArg Variable.there (ih x)
    | arrow a b =>
      cases x with
      | there x => exact congrArg Variable.there (ih x)

theorem oldProject (Γ : List Ty) (x : Variable (groundCtx Γ) .ground) :
    selectGround (oldGround x) = x := by
  induction Γ with
  | nil => exact nomatch x
  | cons σ Γ ih =>
    cases σ with
    | ground =>
      cases x with
      | here => rfl
      | there x => exact congrArg Variable.there (ih x)
    | arrow a b => exact ih x

def castGround {Γ Δ : List Ty} (h : Γ = Δ) (x : Variable Γ .ground) : Variable Δ .ground :=
  cast (congrArg (fun C => Variable C .ground) h) x

theorem castGround_refl {Γ} (x : Variable Γ .ground) : castGround rfl x = x := rfl

theorem castGround_here {Γ Δ} (h : Γ = Δ) :
    castGround (congrArg (List.cons Ty.ground) h) (.here : Variable (.ground :: Γ) .ground) =
      (.here : Variable (.ground :: Δ) .ground) := by
  cases h
  rfl

theorem castGround_there {Γ Δ} {τ : Ty} (h : Γ = Δ) (x : Variable Γ .ground) :
    castGround (congrArg (List.cons τ) h) (.there x) = .there (castGround h x) := by
  cases h
  rfl

theorem oldGroundAll (Γ : List Ty) (hg : ∀ t ∈ Γ, t = .ground) :
    ∀ x : Variable (groundCtx Γ) .ground,
      castGround (groundCtx_of_ground Γ hg) x = oldGround x := by
  induction Γ with
  | nil => intro x; exact nomatch x
  | cons τ Γ ih =>
    obtain rfl : τ = .ground := hg τ (by simp)
    let ht : ∀ t ∈ Γ, t = .ground := fun t hm => hg t (by simp [hm])
    let e := groundCtx_of_ground Γ ht
    intro x
    change Variable (.ground :: groundCtx Γ) .ground at x
    have hEq : groundCtx_of_ground (.ground :: Γ) hg = congrArg (List.cons Ty.ground) e :=
      Subsingleton.elim _ _
    rw [hEq]
    cases x with
    | here => exact castGround_here e
    | there x =>
      rw [castGround_there]
      exact congrArg Variable.there (ih ht x)

theorem oldGroundRemove (left right : List Ty) (σ : Ty) (hs : 0 < σ.level) :
    ∀ x : Variable (groundCtx (left ++ right)) .ground,
      oldGround (castGround (groundCtx_remove left right σ hs).symm x) =
        SelectedBinder.moveFromHead left right σ (.there (oldGround x)) := by
  induction left with
  | nil =>
    intro x
    cases σ with
    | ground => simp [Ty.level] at hs
    | arrow a b =>
      have he : (groundCtx_remove [] right (.arrow a b) hs).symm = rfl :=
        Subsingleton.elim _ _
      rw [he]
      rfl
  | cons a left ih =>
    let e := (groundCtx_remove left right σ hs).symm
    intro x
    cases a with
    | ground =>
      change Variable (.ground :: groundCtx (left ++ right)) .ground at x
      have he : (groundCtx_remove (.ground :: left) right σ hs).symm =
          congrArg (List.cons Ty.ground) e := Subsingleton.elim _ _
      rw [he]
      cases x with
      | here =>
        rw [castGround_here]
        rfl
      | there x =>
        rw [castGround_there]
        exact congrArg Variable.there (ih x)
    | arrow a b =>
      have he : (groundCtx_remove (.arrow a b :: left) right σ hs).symm = e :=
        Subsingleton.elim _ _
      rw [he]
      exact congrArg Variable.there (ih x)

theorem groundProjection : CurrentUnitEliminationTargets.GroundProjection := by
  constructor
  · intro Γ x
    refine ⟨selectGround x,projectOld Γ x,?_⟩
    intro y hy
    rw [← hy]
    exact (oldProject Γ y).symm
  · intro left right σ hs ρ x
    exact congrArg ρ (oldGroundRemove left right σ hs x)

theorem functionsRemovedCount (left right : List Ty) (σ : Ty) (hs : 0 < σ.level) :
    functionalCount (left ++ σ :: right) = functionalCount (left ++ right)+1 := by
  induction left with
  | nil =>
    cases σ with
    | ground => simp [Ty.level] at hs
    | arrow a b => rfl
  | cons a left ih => cases a <;> simp only [List.cons_append,functionalCount,ih]

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination
