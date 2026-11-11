module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathTargets
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion OriginalNonLambdaApplicationPath
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact first-entry decomposition of the original positive path checker,
with no caller-supplied nonempty-list, vertex or certificate witnesses. -/
def ActualOriginalPositivePathFirstStepElimination : Prop :=
  ∀ (data : Data) (oldStep : Program 4), FirstStepCases data oldStep

/-- The original non-lambda rule applies to the first edge of H+, preserving
all first-entry witnesses and the SAME ordinary suffix to the actual endpoint.
The chosen tuple and original requested raw argument remain unchanged. -/
def ActualOriginalNonLambdaApplicationPositivePathElimination : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let r := OriginalApplicationSidecar.finalInputs p
  NonLambdaApplicationPositivePaths (OuterSelection.data r.base r.window) r.window r.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathTargets
