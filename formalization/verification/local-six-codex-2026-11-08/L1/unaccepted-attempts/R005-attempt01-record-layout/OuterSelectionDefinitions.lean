module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelection
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The shared full-mark/bottom tuple is chosen before every finite source
window and Gamma. The existing membership normalization is performed ONCE. -/
def data (base : Data) (window : Program 1) : Data :=
  SourceComputabilityCompletion.SpineApplicationTargets.selectedData base window

/-- Scalar membership is the LITERAL RawScalar.checker of the SAME tuple
used by typedness, quotient edges, actualJ and the original path map. -/
def source (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (base : Data) (oldStep : Program 4) (window : Program 1) : SourcePresentation.Data :=
  let selected := data base window
  Outer.source oldSrc oldComp selected
    (SourceComputabilityCompletion.RawScalar.checker selected) oldStep
    SourceComputabilityCompletion.BottomRepresentative.bottomTest
    SourceComputabilityCompletion.BottomSpineMeasure.measure window

def computability (old : JointGammaComputability.Data) (base : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) : JointGammaComputability.Data :=
  Outer.computability old (data base window) window oldVertex oldResult

def lift (base : Data) (window : Program 1) (oldVertex : Program 5) : Program 5 :=
  Outer.lift (data base window) window oldVertex

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelection
