module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibration
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME final selected tuple, literal bottom/full-spine guards and
complete original positive fallback. This abbreviation makes no new source,
Object, path or certificate encoding, and performs no second normalization. -/
abbrev positive (base : Data) (window : Program 1) (oldStep oldPositive : Program 4) : Program 4 :=
  Outer.positive
    (Outer.rawPositive (OuterSelection.data base window) oldStep
      SourceComputabilityCompletion.BottomRepresentative.bottomTest
      SourceComputabilityCompletion.BottomSpineMeasure.measure)
    window oldPositive

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibration
