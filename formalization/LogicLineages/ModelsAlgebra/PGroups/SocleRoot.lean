module

public import LogicLineages.ModelsAlgebra.PGroups.SocleRootTargets
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitude
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem socle_root_matrix : Targets.groupSocleRootMatrix.{u} := by
  classical
  intro G _ p j n a x y
  simp only [socleRootMatrix, QF.Realize,
    multiple_term_evaluation G ((n + 1) + 1), GroupTerm.eval,
    append, Fin.addCases_left, Fin.addCases_right]
  constructor
  · intro h hx
    by_contra hy
    exact h ⟨hx, hy⟩
  · intro h hbad
    exact hbad.2 (h hbad.1)

theorem socle_root_witness_formula : Targets.groupSocleRootWitnessFormula.{u,v} := by
  intro p j n
  constructor
  · exact Complexity.sigma one_ne_zero {0} (fun _ => 1)
      (fun _ => .qf (socleRootMatrix p j n)) (fun _ => 0)
      (fun _ => zero_lt_one) (fun _ => Complexity.qf .pi _)
  · intro G _ a x
    classical
    change (∃ i : ({0} : Set ℕ), ∃ y : Fin 1 → G,
      (socleRootMatrix p j n).Realize (append (append a x) y)) ↔ _
    constructor
    · rintro ⟨i, y, hy⟩ hx
      exact ⟨y 0, (socle_root_matrix G p j n a x y).mp hy hx⟩
    · intro h
      by_cases hx : p • x 0 = 0
      · obtain ⟨y, hy⟩ := h hx
        exact ⟨⟨0, by simp⟩, (fun _ => y),
          (socle_root_matrix G p j n a x (fun _ => y)).mpr (fun _ => hy)⟩
      · exact ⟨⟨0, by simp⟩, (fun _ => 0),
          (socle_root_matrix G p j n a x (fun _ => 0)).mpr (fun hzero => (hx hzero).elim)⟩

theorem socle_root_formula : Targets.groupSocleRootFormula.{u,v} := by
  intro p j n
  constructor
  · exact Complexity.pi (by simp) {0} (fun _ => 1)
      (fun _ => socleRootWitnessFormula p j n) (fun _ => 1)
      (fun _ => one_lt_two) (fun _ => (socle_root_witness_formula.{u,v} p j n).1)
  · intro G _ a
    change (∀ i : ({0} : Set ℕ), ∀ x : Fin 1 → G,
      (socleRootWitnessFormula p j n).Realize (append a x)) ↔ _
    constructor
    · intro h x hx
      have hroot := ((socle_root_witness_formula.{u,v} p j n).2 G a (fun _ => x)).mp
        (h ⟨0, by simp⟩ (fun _ => x))
      obtain ⟨y, hy⟩ := hroot hx.2
      rw [finite_filtration_multiple_image G p j]
      exact ⟨y, hy⟩
    · intro h i x
      apply ((socle_root_witness_formula.{u,v} p j n).2 G a x).mpr
      intro hx
      have hmem := h (show x 0 ∈ pSocle p (⊤ : AddSubgroup G) from ⟨by trivial, hx⟩)
      rw [finite_filtration_multiple_image G p j] at hmem
      obtain ⟨y, hy⟩ := hmem
      exact ⟨y, by simpa only [nsmulAddMonoidHom_apply] using hy⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
