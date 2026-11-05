module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitNumericCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitNumericProgramsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.StatementChecks

theorem gate_code_calibration : Targets.GateCodeCalibration := Proof.gateCodeCalibration
theorem system_code_calibration : Targets.SystemCodeCalibration := Proof.systemCodeCalibration
theorem system_code_primitive : Targets.SystemCodePrimitive := Proof.systemCodePrimitive
theorem encoder_primitive : Targets.EncoderPrimitive := Proof.encoderPrimitive
theorem encoder_calibration : Targets.EncoderCalibration := Proof.encoderCalibration

theorem numeric_circuit_encoder : CircuitLinear.Targets.NumericCircuitEncoder :=
  ⟨encode, Proof.encoderPrimitive, Proof.encoderCalibration⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.StatementChecks
