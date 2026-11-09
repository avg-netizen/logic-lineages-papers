module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceTargets

/-- Generic N/T/scalar/actualJ slice congruence. Later ALL-input decoded
leaf/validity calibrations pay Atomic at raw p and the canonical parameter
of its ACTUAL decoded context. No rawContext=encode(decodedContext), type,
source-validity, successful run or canonical-input assumption is added. -/
def ActualOriginalCompositeParameterSliceCongruence : Prop :=
  ∀ (data : InternalOriginalUniformDescentSelection.Data) (p q : Nat),
    ParameterSlice.Atomic data p q → ParameterSlice.Composite data p q

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceTargets
