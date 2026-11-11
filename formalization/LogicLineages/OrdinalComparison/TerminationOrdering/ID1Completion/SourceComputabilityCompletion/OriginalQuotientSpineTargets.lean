module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineTargets
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion OriginalQuotientSpine
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Generic arithmetic transport through the original quotient checker.
The two internal suppliers remain explicit here; the concrete final-tuple
target below discharges both without a native-reflection rule or new source
premise. Full-mark preservation includes the depth, not only the flag. -/
def ActualOriginalQuotientSpineTransport : Prop :=
  ∀ (data : Data) (window : Program 1) (oldStep : Program 4),
    OriginalFullFoldSpine.FullFoldMarkPreservation data window →
    OriginalSelectedStepSpine.RawStepHasSpineGuard data oldStep →
    QuotientHasSpineGuard data window oldStep

/-- Refine the old leaf once and retain the SAME unchanged finalInputs
pipeline and selected Data. Both internal suppliers are discharged at this
literal tuple. No raw witness, fold law, native calibration assumption,
non-bottom assumption or strengthened source relation is added to the caller.
This is a supporting quotient guard law, not an original positive certificate. -/
def ActualOriginalFinalQuotientSpineGuard : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  QuotientHasSpineGuard (OuterSelection.data r.base r.window) r.window r.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineTargets
