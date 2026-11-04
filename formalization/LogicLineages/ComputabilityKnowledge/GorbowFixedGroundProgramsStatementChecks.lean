module

public import LogicLineages.ComputabilityKnowledge.GorbowFixedGroundProgramsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms.StatementChecks

theorem fullFixedGround : Targets.Target := Proof.fullTarget
theorem singleProgram : Targets.SingleProgram := fullFixedGround.1
theorem fixedRegistry : Targets.FixedRegistry := fullFixedGround.2.1
theorem definingDispatcher : Targets.DefiningDispatcher := fullFixedGround.2.2.1
theorem namedOverlay : Targets.NamedOverlay := fullFixedGround.2.2.2.1
theorem actualPrograms : Targets.ActualPrograms := fullFixedGround.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms
