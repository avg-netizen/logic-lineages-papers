module
public import LogicLineages.OrdinalComparison.WWUnitObservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitObservation.StatementChecks
 theorem positiveValue : Targets.PositiveValue := Proof.positiveValue
 theorem groundValue : Targets.GroundValue := Proof.groundValue
 theorem functionalCoordinates : Targets.FunctionalCoordinates := Proof.functionalCoordinates
 theorem selectedTransport : Targets.SelectedTransport := Proof.selectedTransport
 theorem selectedValuation : Targets.SelectedValuation := Proof.selectedValuation
end LogicLineages.OrdinalComparison.Source.UnitObservation.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.UnitObservation
