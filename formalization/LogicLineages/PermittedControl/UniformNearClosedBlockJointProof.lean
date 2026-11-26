module
public import LogicLineages.PermittedControl.UniformGroundAssemblyTargets
import LogicLineages.PermittedControl.UniformNearClosedBlockProof

public section
namespace LogicLineages.PermittedControl.UniformNearClosedBlock

/-- Root's frozen `UniformGroundAssembly.JointNearClosedBlocks`, from Part 1. -/
theorem jointNearClosedBlocks : UniformGroundAssembly.JointNearClosedBlocks :=
  uniformNearClosedBlockDecision

#print axioms jointNearClosedBlocks

end LogicLineages.PermittedControl.UniformNearClosedBlock
