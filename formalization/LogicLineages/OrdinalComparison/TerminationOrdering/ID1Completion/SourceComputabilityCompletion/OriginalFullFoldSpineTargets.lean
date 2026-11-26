module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineTargets
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion OriginalFullFoldSpine
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The EXISTING selected tuple preserves the full bottom-spine mark through
its SAME original canonical fold. No new Program refinement, native
calibration premise or assumed fold invariant is introduced. -/
def ActualOriginalFullFoldSpinePreservation : Prop :=
  ∀ (base : Data) (window : Program 1),
  FullFoldMarkPreservation (SpineApplicationTargets.selectedData base window) window

/-- Specialize to the SAME final tuple already used by the complete source
package, its quotient checker, actualJ, and the accepted Object/path laws. -/
def ActualOriginalFinalFullFoldSpinePreservation : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let r := OriginalApplicationSidecar.finalInputs p
  FullFoldMarkPreservation (OuterSelection.data r.base r.window) r.window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineTargets
