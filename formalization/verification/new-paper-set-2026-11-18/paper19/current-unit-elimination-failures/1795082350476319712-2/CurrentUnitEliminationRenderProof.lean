module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationActiveProof
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationGroundProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open CurrentOneUnit GroundEquivalence

theorem castHoldsRaw (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ Δ : List Ty}
    (e : Γ = Δ) (q : OpenGraph Γ) (ρ : Variable Δ .ground → Nat) (n : Nat) :
    HoldsRaw p f (e ▸ q : OpenGraph Δ) ρ n ↔
      HoldsRaw p f q (fun x => ρ (castGround e x)) n := by
  cases e
  rfl

private theorem castConjunctive {Γ Δ : List Ty} (e : Γ = Δ) (g : OpenGraph Γ)
    (h : Conjunctive g.matrix) : Conjunctive (e ▸ g : OpenGraph Δ).matrix := by
  cases e
  exact h

theorem renderConjunctive (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty} (q : Tree Γ) :
    Conjunctive (render p f q).matrix := by
  induction q with
  | leaf hg a => exact castConjunctive _ _ (groundConjunctive p f hg a)
  | free left right σ hs row q ih => exact castConjunctive _ _ (freeConjunctive row _ ih)
  | active left right σ hs row q s ih ih' => exact castConjunctive _ _ (activeConjunctive row _ _ ih ih')

theorem treeHoldsGround (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty} {τ : Ty}
    (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) (ρ : Variable Γ .ground → Nat) (r : Nat) :
    (Tree.leaf hg a).holds p f ρ r ↔ HoldsRaw p f (groundGraph p f hg a) ρ r := by
  let e := (groundCtx_of_ground Γ hg).symm
  change HoldsRaw p f (e ▸ groundGraph p f hg a : OpenGraph (groundCtx Γ))
    (fun x => ρ (oldGround x)) r ↔ _
  rw [castHoldsRaw]
  have hρ : (fun x => ρ (oldGround (castGround e x))) = ρ := by
    funext x
    rw [← oldGroundAll Γ hg (castGround e x)]
    exact congrArg ρ (castGround_left_inverse e x)
  rw [hρ]

theorem treeHoldsFree (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (left right : List Ty) (σ : Ty) (hs : 0 < σ.level) (row : LinearCode) (q : Tree (left ++ right))
    (ρ : Variable (left ++ σ :: right) .ground → Nat) (n : Nat) :
    (Tree.free left right σ hs row q).holds p f ρ (n+1) ↔
      ∃ l : Nat, q.holds p f (UnitObservation.remainingInputs left right σ ρ) l ∧ holds row l 0 (n+1) := by
  let e := (groundCtx_remove left right σ hs).symm
  let μ := fun x : Variable (groundCtx (left ++ right)) .ground =>
    UnitObservation.remainingInputs left right σ ρ (oldGround x)
  change HoldsRaw p f (e ▸ freeGraph row (render p f q) : OpenGraph (groundCtx (left ++ σ :: right)))
    (fun x => ρ (oldGround x)) (n+1) ↔ _
  rw [castHoldsRaw]
  have he : (fun x => ρ (oldGround (castGround e x))) = μ := by
    funext x
    exact congrArg ρ (oldGroundRemove left right σ hs x)
  rw [he]
  exact (exactComposition p f _ μ row n (render p f q) (render p f q)).1

theorem treeHoldsActive (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (left right : List Ty) (σ : Ty) (hs : 0 < σ.level) (row : LinearCode) (q s : Tree (left ++ right))
    (ρ : Variable (left ++ σ :: right) .ground → Nat) (n : Nat) :
    (Tree.active left right σ hs row q s).holds p f ρ (n+1) ↔
      ∃ l l' : Nat, q.holds p f (UnitObservation.remainingInputs left right σ ρ) l ∧
        s.holds p f (UnitObservation.remainingInputs left right σ ρ) l' ∧ holds row l l' (n+1) := by
  let e := (groundCtx_remove left right σ hs).symm
  let μ := fun x : Variable (groundCtx (left ++ right)) .ground =>
    UnitObservation.remainingInputs left right σ ρ (oldGround x)
  change HoldsRaw p f (e ▸ activeGraph row (render p f q) (render p f s) :
    OpenGraph (groundCtx (left ++ σ :: right))) (fun x => ρ (oldGround x)) (n+1) ↔ _
  rw [castHoldsRaw]
  have he : (fun x => ρ (oldGround (castGround e x))) = μ := by
    funext x
    exact congrArg ρ (oldGroundRemove left right σ hs x)
  rw [he]
  exact (exactComposition p f _ μ row n (render p f q) (render p f s)).2

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination
