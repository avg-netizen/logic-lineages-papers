module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation.StatementChecks

theorem calibratedExistence : Targets.CalibratedExistence := Proof.calibratedExistence
theorem closedEquation : Targets.ClosedEquation := Proof.closedEquation
theorem fixedPoint : Targets.FixedPoint := Proof.fixedPoint
theorem originalName : Targets.OriginalName := Proof.originalName
theorem consistency : Targets.Consistency := Proof.consistency

end LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation.StatementChecks
