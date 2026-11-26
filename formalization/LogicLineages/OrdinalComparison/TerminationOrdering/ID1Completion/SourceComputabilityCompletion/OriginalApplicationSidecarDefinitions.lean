module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecar
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The PREVIOUS checked selection pipeline. This Data does not refer to
any sidecar refinement or to the eventual final input tuple. -/
def originalData (data : Data) (window : Program 1) : Data :=
  OriginalFunctionNeutrality.selectedData data window

/-- The original bounded stack, at the previous guard and selected leaf,
with only the literal raw application as combiner. This acyclic sidecar is
not a replacement for the final source's full canonical fold. -/
def fold (data : Data) (window : Program 1) : Program 2 :=
  InternalParameterizedApplicationResultStack.foldP
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))
    (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    InternalParameterizedCanonicalResultFold.rawApplicationAt

/-- The inactive branch retains the WHOLE old representative output,
including malformed and nonclosed-window cases. All-input native equality
must separately justify the active sidecar branch. -/
def representative (data : Data) (window : Program 1) : Program 2 :=
  InternalAcceptance.branch (OriginalFunctionNeutrality.active data window)
    data.oldRepresentative (fold data window)

def baseData (data : Data) (window : Program 1) : Data :=
  { data with oldRepresentative := representative data window }

/-- The original pipeline is applied to the once-refined original base.
No source, target, member, observer, fuel or constructor AST is replaced. -/
def selectedData (data : Data) (window : Program 1) : Data :=
  OriginalFunctionNeutrality.selectedData (baseData data window) window

def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := baseData p.base p.window }

/-- Start from one ORIGINAL globally calibrated tuple, before all finite
windows and Gamma. In particular the existing oldStep refinement occurs
once, through the original finalInputs pipeline. -/
def finalInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  OriginalFunctionNeutrality.finalInputs (refineInputs p)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecar
