module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibration
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native all-input calibration of the literal original paired result and
application constructor on the SAME selected readyData. This is a contract
for explicit global inputs, not a complete source-program existence claim. -/
structure Calibrated (n : Nat) (arity : Fin n → Nat)
    (base : Data) (window : Program 1) (old : JointGammaComputability.Data)
    (oldVertex oldResult : Program 5) : Prop where
  result : ∀ v : List.Vector Nat 5,
    evaluate (Outer.result old (OuterSelection.data base window) window oldVertex oldResult) v =
      ApplicationResultBuilder.resultValue n arity v
  computability : JointGammaComputability.Calibrated
    (OuterSelection.computability old base window oldVertex oldResult) n arity

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibration
