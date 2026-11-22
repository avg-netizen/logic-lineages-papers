module
public import LogicLineages.PermittedControl.AffineCollapseGraphCompositionTargets
import LogicLineages.PermittedControl.AffineCollapseGraphCompositionPairProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGraphComposition

theorem exactTestPolarity : ExactTestPolarity := by
  intro f B selected head e inputName outputName ν fresh test
  have extension := (exactPairExtension f B selected head e inputName outputName ν fresh).1
  have transfer (property : (Nat → Nat) → Prop) :
      (∃ values : Nat × Nat,
        let θ := insertValues ν inputName outputName values
        graph f head e inputName outputName θ ∧ property θ) ↔
        originalDomain head e ν ∧
          property (insertValues ν inputName outputName (originalValues f head e ν)) := by
    constructor
    · rintro ⟨values,holds,testHolds⟩
      rcases (extension values).mp holds with ⟨domain,rfl⟩
      exact ⟨domain,testHolds⟩
    · rintro ⟨domain,testHolds⟩
      exact ⟨originalValues f head e ν,(extension _).mpr ⟨domain,rfl⟩,testHolds⟩
  exact ⟨transfer test,transfer (fun θ => ¬ test θ)⟩

end LogicLineages.PermittedControl.AffineCollapseGraphComposition
