module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionCalibrationProof
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityCompletion
open InternalOriginalUniformContextMembership (normalizeData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- This is the exact tuple BEFORE its single membership normalization.
All choices, including the literal shared window Program, precede every
concrete source window and Gamma. -/
def preData (base : Data) (window : Program 1) : Data :=
  BottomRepresentative.baseData
    (BottomParameter.baseData (SpineRepresentative.baseData base window)) window

theorem selectedData (base : Data) (window : Program 1) :
    OuterSelection.data base window = normalizeData (preData base window) := rfl

/-- Compose the checked ALL-input leaf calibrations. This is native
metadata for the SAME tuple; it never reflects truth of an open graph into
an internal arithmetic derivation. -/
theorem preCalibrated (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : Path.windowCalibrated n window) :
    InternalOriginalUniformDescentSelection.Calibrated n arity (preData base window) := by
  have hs := SpineRepresentativeEvaluationProof.actualOriginalSpineRepresentativeCalibration
    n arity base window hc hw
  have hp := BottomParameterEvaluationProof.actualOriginalBottomParameterCalibration
    n arity (SpineRepresentative.baseData base window) hs
  exact (BottomRepresentativeEvaluationProof.actualOriginalBottomRepresentativeCalibration
    n arity (BottomParameter.baseData (SpineRepresentative.baseData base window)) window hp hw).1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionCalibrationProof
