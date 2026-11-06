module
public import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.Targets
import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ProgramsProof
public meta import LogicLineages.Audit
public section
namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ProgramsStatementChecks

theorem framing_program : Targets.FramingProgram := ProgramsProof.framingProgram
theorem scalar_validation : Targets.ScalarValidation := ProgramsProof.scalarValidation
theorem scalar_programs : Targets.ScalarPrograms := ProgramsProof.scalarPrograms
theorem scalar_calibration : Targets.ScalarCalibration := ProgramsProof.scalarCalibration
theorem vector_programs : Targets.VectorPrograms := ProgramsProof.vectorPrograms
theorem vector_calibration : Targets.VectorCalibration := ProgramsProof.vectorCalibration

end LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ProgramsStatementChecks
#audit_namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ProgramsStatementChecks
