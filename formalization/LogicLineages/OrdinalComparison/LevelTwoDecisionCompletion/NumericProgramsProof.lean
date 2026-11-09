module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProgramsProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionCodeProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineLeastProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.ProgramsProof
open LevelTwoCounterexample
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair
attribute [local irreducible] ClosedWordDecisionCompletion.Machine.solve Admission.compile Code.matrix

/-- The closed-word solver is joint in degree and code; neither is fixed
outside the input to this composition. -/
theorem packageCounterexample_computable : Computable packageCounterexample :=
  ClosedWordDecisionCompletion.MachinePrograms.solve_computable.comp
    ((Computable.fst.comp Computable.fst).pair CodePrograms.actualMatrixProgram.to_comp)

attribute [local irreducible] packageCounterexample

theorem decision_computable : Computable decision :=
  Computable.option_map AdmissionCodeProof.compile_primitive.to_comp
    (Primrec.not.to_comp.comp (packageCounterexample_computable.comp Computable.snd)).to₂

attribute [local irreducible] decision

theorem solve_computable : Computable solve :=
  Computable.option_getD decision_computable (Computable.const false)

theorem actualNumericPrograms : Targets.ActualNumericPrograms :=
  ⟨packageCounterexample_computable,decision_computable,solve_computable⟩

#print axioms packageCounterexample_computable
#print axioms decision_computable
#print axioms solve_computable
#print axioms actualNumericPrograms

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.ProgramsProof
