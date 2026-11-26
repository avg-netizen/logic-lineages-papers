module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Supporting domain bridge for the already frozen structural traversal.
Only its actual new leaf source and original window are premises. No old
activation, old validity, calibration or key coherence is assumed. -/
def ActivationLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let r := OriginalStructuralTraversalKey.refined p H G W P
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
      graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.leafData r.base r.window))
        InternalOriginalStepGuard.one input parameter).imp
      (OriginalStructuralClassKeyDefinitions.Active p H G W input parameter)))

def ActualOriginalStructuralKeyActivation : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    ActivationLaw p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationTargets
