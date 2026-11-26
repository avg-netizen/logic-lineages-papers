module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeProof
open WholeBoundProjectionCode

theorem literalInitializedProjection : WholeBoundProjectionCodeTargets.LiteralInitializedProjection := by
  intro bound p
  exact (congrArg (PlainBlockProjectionCode.project bound)
    (WholeBoundInitializationCodeProof.literalFormulaCalibration bound p)).trans
      (PlainBlockProjectionCodeProof.literalProjectorCalibration bound
        (WholeBoundInitialization.«initialize» bound p))
#print axioms literalInitializedProjection

attribute [local irreducible] Computable Partrec
attribute [local irreducible] WholeBoundInitializationCode.formula PlainBlockProjectionCode.project

theorem actualJointProgram : WholeBoundProjectionCodeTargets.ActualJointProgram := by
  change Computable (fun p : List Nat × Nat => project p.1 p.2)
  unfold project
  have hi : Computable (fun p : List Nat × Nat => WholeBoundInitializationCode.formula p.1 p.2) :=
    WholeBoundInitializationCodeProof.actualFormulaProgram
  have hp : Computable (fun p : List Nat × Nat => PlainBlockProjectionCode.project p.1 p.2) :=
    PlainBlockProjectionCodeProof.project_computable
  exact hp.comp (Computable.fst.pair hi)
#print axioms actualJointProgram

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeProof
