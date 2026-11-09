module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathTargets
open UniformCertificateCompletion OriginalVariableQuotientPath

/-- Same final globally refined Inputs, same literal OuterSelection pipeline.
Bottom recognition in BOTH directions is derived at the full fold, not
assumed from an abstract package or substituted by a new observer guard. -/
def ActualOriginalFullFoldBottomPreservation : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs),
    let r := OriginalVariableRepresentative.refineInputs p
    FullFoldBottomPreservation (OuterSelection.data r.base r.window) r.window

/-- Actual original quotient certificates are opened internally. The paid
reverse variable fold law and actual normalized raw-step constructor cases
must be applied with derived graph premises at this SAME final tuple. -/
def ActualOriginalQuotientConstructorCases : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs),
    let r := OriginalVariableRepresentative.refineInputs p
    QuotientConstructorCases (OuterSelection.data r.base r.window) r.oldStep r.window

/-- The ORIGINAL raw-list positive/reflexive path Programs are retained.
This is a direct actual-source conclusion with no assumed edge law, terminal
state axiom, native path interpretation or generic path-correctness premise. -/
def ActualOriginalPathConstructorCases : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs),
    let r := OriginalVariableRepresentative.refineInputs p
    PathConstructorCases (OuterSelection.data r.base r.window) r.oldStep r.window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathTargets
