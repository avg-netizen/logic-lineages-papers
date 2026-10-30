module

public import LogicLineages.ModelsAlgebra.PGroups.AnnihilationTargets
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitude
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem annihilation_formula : Targets.groupAnnihilationFormula.{u,v} := by
  intro c n
  constructor
  · exact Complexity.pi one_ne_zero {0} (fun _ => 1)
      (fun _ => .qf (.equal (multipleTerm c (.var (Fin.natAdd n (0 : Fin 1)))) .zero))
      (fun _ => 0) (fun _ => zero_lt_one) (fun _ => Complexity.qf .sigma _)
  · intro G _ a
    change (∀ i : ({0} : Set ℕ), ∀ d : Fin 1 → G,
      (multipleTerm c (.var (Fin.natAdd n (0 : Fin 1)))).eval (append a d) = 0) ↔ _
    simp only [multiple_term_evaluation G (n + 1) c, GroupTerm.eval, append, Fin.addCases_right]
    constructor
    · intro h x
      exact h ⟨0, by simp⟩ (fun _ => x)
    · intro h i d
      exact h (d 0)

theorem finite_exponent_formula : Targets.groupFiniteExponentFormula.{u} := by
  intro G _ p j n a
  rw [(annihilation_formula.{u,0} (p ^ j) n).2 G a, finite_filtration_multiple_image G p j]
  constructor
  · intro h
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      change p ^ j • y = 0
      exact h y
    · exact bot_le
  · intro h x
    have hx : p ^ j • x ∈ multipleImage G (p ^ j) := ⟨x, rfl⟩
    rw [h] at hx
    exact hx

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
