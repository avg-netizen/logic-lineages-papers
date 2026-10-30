module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirStageTargets
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Data.Finset.Range
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem reservoir_stage_isomorphism : Targets.groupReservoirStageIsomorphism := by
  classical
  intro A B C _ _ _ i
  let f : reservoirStage A B C i →+ A × ((Fin i → B) × (ℕ →₀ C)) :=
    { toFun := fun x => (x.val.1, (fun n => x.val.2.1 n.val, x.val.2.2))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.1) h
    apply Prod.ext
    swap
    · exact congrArg (fun z => z.2.2) h
    ext n
    by_cases hn : n < i
    · exact congrArg (fun z : A × ((Fin i → B) × (ℕ →₀ C)) => z.2.1 ⟨n,hn⟩) h
    · rw [x.property n (Nat.le_of_not_gt hn), y.property n (Nat.le_of_not_gt hn)]
  have hsurj : Function.Surjective f := by
    rintro ⟨a,b,c⟩
    let v : ℕ → B := fun n => if h : n < i then b ⟨n,h⟩ else 0
    let x : ℕ →₀ B := Finsupp.onFinset (Finset.range i) v (by
      intro n hn
      apply Finset.mem_range.mpr
      by_contra h
      exact hn (by simp [v,h]))
    have hx : (a,(x,c)) ∈ reservoirStage A B C i := by
      intro n hn
      change v n = 0
      simp [v,not_lt_of_ge hn]
    refine ⟨⟨(a,(x,c)),hx⟩, ?_⟩
    apply Prod.ext
    · rfl
    apply Prod.ext
    swap
    · rfl
    funext n
    change v n.val = b n
    simp [v,n.isLt]
  exact ⟨AddEquiv.ofBijective f ⟨hinj,hsurj⟩⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
