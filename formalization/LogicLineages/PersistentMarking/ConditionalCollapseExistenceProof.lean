module

public import LogicLineages.PersistentMarking.ConditionalCollapseExistenceTargets

public section

namespace LogicLineages.PersistentMarking.ConditionalCollapseExistence
open ConditionalTowerCofinality

universe u v

theorem solvableIffSolvableBelow : SolvableIffSolvableBelow.{u,v} := by
  intro I O _ _ norm critical
  constructor
  · intro hs ξ prev
    obtain ⟨θ, hc, h⟩ := hs ξ (fun η => if h : η < ξ then prev η h else norm ξ)
    refine ⟨θ, hc, fun η hη hn => ?_⟩
    have h' := h η hη hn
    simpa [hη] using h'
  · intro hs ξ prev
    exact hs ξ (fun η _ => prev η)

theorem characterizationExistsBelow : CharacterizationExistsBelow.{u,v} := by
  intro I O _ _ _ _ norm critical one endpoint a hs
  -- the least critical value satisfying the clause for given earlier values
  have hmin : ∀ (ξ : I) (prev : (η : I) → η < ξ → O),
      ∃ θ, (critical θ ∧ ∀ η (h : η < ξ), norm η < θ → prev η h < θ) ∧
        ∀ θ', (critical θ' ∧ ∀ η (h : η < ξ), norm η < θ' → prev η h < θ') → θ ≤ θ' := by
    intro ξ prev
    obtain ⟨θ, hθ, hleast⟩ := (wellFounded_lt (α := O)).has_min
      {θ | critical θ ∧ ∀ η (h : η < ξ), norm η < θ → prev η h < θ} (hs ξ prev)
    exact ⟨θ, hθ, fun θ' hθ' => not_lt.mp (hleast θ' hθ')⟩
  choose F hF hFmin using hmin
  -- well-founded recursion on the index
  obtain ⟨psi, hpsi⟩ : ∃ psi : I → O, ∀ ξ, psi ξ = F ξ (fun η _ => psi η) :=
    ⟨WellFounded.fix (C := fun _ => O) (wellFounded_lt (α := I)) F,
      fun ξ => WellFounded.fix_eq (C := fun _ => O) (wellFounded_lt (α := I)) F ξ⟩
  refine ⟨psi, fun ξ => ?_⟩
  have h1 := hF ξ (fun η _ => psi η)
  have h2 := hFmin ξ (fun η _ => psi η)
  rw [← hpsi ξ] at h1 h2
  exact ⟨h1.1, h1.2, fun θ hc hθ => h2 θ ⟨hc, hθ⟩⟩

theorem characterizationExists : CharacterizationExists.{u,v} := by
  intro I O _ _ _ _ norm critical one endpoint a hs
  exact characterizationExistsBelow.{u,v} I O norm critical one endpoint a
    ((solvableIffSolvableBelow.{u,v} I O norm critical).mp hs)

#print axioms solvableIffSolvableBelow
#print axioms characterizationExistsBelow
#print axioms characterizationExists
end LogicLineages.PersistentMarking.ConditionalCollapseExistence
