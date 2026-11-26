module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Equality of the original compiled arithmetic graphs, internally for
every actual output and input. This supplies no numerical-truth reflection. -/
def ProgramGraphEquivalent {n : Nat} (p q : Program n) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out : OTerm alpha) (xs : Fin n → OTerm alpha),
  Nonempty (Derivation body Delta
    ((programGraph p out xs).iff (programGraph q out xs)))

def ActualClosedEndpointTransport : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (oldStep : Program 4) (window : Program 1),
  ProgramGraphEquivalent
    (OriginalHereditaryLambdaGlobal.closedLeaf
      (InternalParameterizedStructuralEndpointGuard.selectedEndpoint
        (OriginalTransparentDecoderValidatorCollapse.selected p H G W)) window oldStep)
    (OriginalHereditaryLambdaGlobal.closedLeaf
      (OriginalMixedLiteralEndpointDefinitions.endpoint H G
        (InternalOriginalUniformContextMembership.contextMember p.base.member) W) window oldStep)

/-- Exact final tuple already named by the retained prepared active-kernel
package. No compiler, source, representative or endpoint is selected anew. -/
def preparedKernelFinalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : GlobalSourcePackage.Inputs :=
  let q := OriginalMixedPrepared.prepared p H G W
  let K := OriginalActiveClassKernel.classTest q H G W P
  let Q := OriginalActiveObservedClass.classTest q H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw K
  let seed := OriginalTransparentMinimum.minimumInputs H G Q q
  OriginalLambdaTraversalSelection.finalInputs (OriginalFinalGuardedRank.refined seed H G W)

/-- The actual final effective leaf in the SAME prepared active-kernel
package, internally identified with the explicit C checker on all raw vectors.
All failed tests and all original path states must be retained by the proof. -/
def ActualPreparedKernelClosedChecker : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
  ProgramGraphEquivalent (preparedKernelFinalInputs p H G W P).oldStep
    (OriginalMixedClosedTraceDefinitions.checker H G
      (InternalOriginalUniformContextMembership.contextMember p.base.member)
      W p.oldStep p.window)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration
