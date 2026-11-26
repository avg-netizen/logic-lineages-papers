module
public import LogicLineages.PermittedControl.UniformGroundComparisonTargets
import LogicLineages.PermittedControl.UniformGroundAssemblyProof
import LogicLineages.PermittedControl.UniformPolicyCompilerProof
import LogicLineages.PermittedControl.UniformNearClosedBlockJointProof

public section
namespace LogicLineages.PermittedControl.UniformGroundComparison

/-- Clause (i) of Paper 17 `thm:main` with the printed uniformity,
unconditional. -/
theorem uniformGroundComparison : UniformGroundComparison :=
  UniformGroundAssembly.exactUniformGroundFromPieces
    UniformPolicyCompiler.exactUniformCompiler UniformNearClosedBlock.jointNearClosedBlocks

/-- The strengthened comparator for Paper 17 `thm:main`, unconditional. -/
theorem uniformMainComparison : UniformMainComparison :=
  UniformGroundAssembly.exactUniformMainFromPieces
    UniformPolicyCompiler.exactUniformCompiler UniformNearClosedBlock.jointNearClosedBlocks

#print axioms uniformGroundComparison
#print axioms uniformMainComparison
end LogicLineages.PermittedControl.UniformGroundComparison
