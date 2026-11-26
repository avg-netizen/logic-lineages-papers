module
public import LogicLineages.StandardControlCurrent.PolicyShapeSyntaxProof
public import LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyShapeStatementChecks
theorem full : PolicyShapeTargets.FullPolicyShape :=
  ⟨PolicyShapeSyntaxProof.sites,PolicyShapeSyntaxProof.framed,
    PolicyShapeProgramsProof.raw,PolicyShapeProgramsProof.policies,PolicyShapeSyntaxProof.literal⟩
#print axioms full
end LogicLineages.StandardControlCurrent.PolicyShapeStatementChecks
