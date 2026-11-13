module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootActivationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem activeFromSource (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (input parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph
        (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window input parameter)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.leafData
          (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).base
          (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window))
        InternalOriginalStepGuard.one input parameter))) :
    Nonempty (Derivation body Delta
      (OriginalStructuralClassKeyDefinitions.Active p H G W input parameter)) := by
  have hq := OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P input parameter hs
  have hold := OriginalStructuralKeyActivationProof.oldLeafSource p H G W input parameter hq
  change Nonempty (Derivation body Delta
    (graph2 (OriginalFunctionNeutrality.active
      (OriginalLambdaTraversalSelection.transparentData
        (OriginalStructuralClassKeyDefinitions.prior p H G W).base) p.window)
      InternalOriginalStepGuard.one input parameter))
  rw [OriginalLambdaTraversalFinalGuardProof.activeLeaf]
  exact InternalAcceptanceConjunctionProof.conjunctionAccept _ _
    (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hold
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootActivationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootActivationProof
