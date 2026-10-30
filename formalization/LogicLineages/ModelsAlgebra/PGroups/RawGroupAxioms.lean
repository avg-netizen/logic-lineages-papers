module
public import LogicLineages.ModelsAlgebra.PGroups.RawGroupAxiomsTargets
public import Mathlib.Algebra.Group.MinimalAxioms
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u

theorem raw_axioms_complexity : Targets.groupRawAxiomsComplexity := by
  exact Complexity.pi one_ne_zero {0} (fun _ => 3) (fun _ => .qf abelianGroupMatrix)
    (fun _ => 0) (fun _ => zero_lt_one) (fun _ => Complexity.qf .sigma _)

theorem raw_axioms_realization : Targets.groupRawAxiomsRealization.{u} := by
  intro G R
  change (∀ i : ({0} : Set ℕ), ∀ d : Fin 3 → G,
    (R.add (R.add (d 0) (d 1)) (d 2) = R.add (d 0) (R.add (d 1) (d 2))) ∧
    (R.add (d 0) (d 1) = R.add (d 1) (d 0)) ∧
    (R.add R.zero (d 0) = d 0) ∧ (R.add (R.neg (d 0)) (d 0) = R.zero)) ↔ _
  let tuple (x y z : G) : Fin 3 → G := fun i => if i = 0 then x else if i = 1 then y else z
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · intro x y z
      simpa [tuple] using
        (h ⟨0,by simp⟩ (tuple x y z)).1
    · intro x y
      simpa [tuple] using (h ⟨0,by simp⟩ (tuple x y R.zero)).2.1
    · intro x
      exact (h ⟨0,by simp⟩ (fun _ => x)).2.2.1
    · intro x
      exact (h ⟨0,by simp⟩ (fun _ => x)).2.2.2
  · intro h i d
    exact ⟨h.1 (d 0) (d 1) (d 2), h.2.1 (d 0) (d 1), h.2.2.1 (d 0), h.2.2.2 (d 0)⟩

theorem raw_laws_group_construction : Targets.groupRawLawsGroupConstruction.{u} := by
  intro G R h
  letI : Zero G := ⟨R.zero⟩
  letI : Neg G := ⟨R.neg⟩
  letI : Add G := ⟨R.add⟩
  let g : AddGroup G := AddGroup.ofLeftAxioms h.1 h.2.2.1 h.2.2.2
  let c : AddCommGroup G := { g with add_comm := h.2.1 }
  exact ⟨c,rfl⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
