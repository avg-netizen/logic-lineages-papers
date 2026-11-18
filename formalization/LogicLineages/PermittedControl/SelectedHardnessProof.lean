module
public import LogicLineages.PermittedControl.SelectedHardnessSignedProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessProof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedHardness

theorem combinatorValues : SelectedHardnessTargets.CombinatorValues := by
  intro ctrl K hc Γ p ρ a b
  refine ⟨?_,SelectedHardnessValuesProof.project_head ctrl K hc p ρ a b,
    SelectedHardnessValuesProof.combine_head ctrl K hc p ρ a b,
    SelectedHardnessValuesProof.combine_scalar ctrl K hc p ρ a b,
    SelectedHardnessSignedProof.lift_head ctrl K hc p ρ a⟩
  rw [SelectedHardnessCoordinatesProof.value1_of_assignment ctrl p ρ _ _
    (SelectedHardnessPairSyntaxProof.identity_assignment p Γ)]
  rfl

theorem selectedHardnessCombinators : SelectedHardnessTargets.SelectedHardnessCombinators :=
  ⟨SelectedHardnessCoordinatesProof.coordinateFacts,combinatorValues,
    SelectedHardnessSignedProof.signedCombinatorValues⟩
end LogicLineages.PermittedControl.SelectedHardnessProof
