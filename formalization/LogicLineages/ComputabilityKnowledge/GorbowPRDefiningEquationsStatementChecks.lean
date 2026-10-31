module

public import LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquationsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations.StatementChecks

theorem headerCalibration : Targets.HeaderCalibration := Proof.headerCalibration
theorem termCalibration : Targets.TermCalibration := Proof.termCalibration
theorem nodeEquationsSound : Targets.NodeEquationsSound := Proof.nodeEquationsSound
theorem allAxiomsSound : Targets.AllAxiomsSound := Proof.allAxiomsSound
theorem checkExact : Targets.CheckExact := Proof.checkExact
theorem fixedCheckerPrimitive : Targets.FixedCheckerPrimitive := Proof.fixedCheckerPrimitive
theorem theorySoundness : Targets.TheorySoundness := Proof.theorySoundness

end LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations.StatementChecks
