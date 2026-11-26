module
public import LogicLineages.PermittedControl.GroundComparisonMainTargets
import LogicLineages.PermittedControl.GroundComparisonProof
import LogicLineages.PermittedControl.ControlProof
import LogicLineages.PermittedControl.NearControlProof
import LogicLineages.PermittedControl.SelectedFunctionalHardnessProof

public section
namespace LogicLineages.PermittedControl.GroundComparisonMain

/-- Paper 17 `thm:main` comparator, unconditional. -/
theorem mainComparison : MainComparison :=
  ⟨fullControl,nearControlModular,GroundComparison.groundComparison,
    SelectedFunctionalHardness.Proof.selectedFunctionalHardness⟩

#print axioms mainComparison
end LogicLineages.PermittedControl.GroundComparisonMain
