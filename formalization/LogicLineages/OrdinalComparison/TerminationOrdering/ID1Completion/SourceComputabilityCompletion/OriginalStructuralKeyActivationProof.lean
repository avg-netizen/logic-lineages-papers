module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationTargetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover the old transparent leaf source from its original guarded decoder.
HT and HS are paid independently, then reassembled at the actual old leaf. -/
theorem oldLeafSource (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (input parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (OriginalStructuralClassKeyDefinitions.prior p H G W).base.oldSource
        (numeral 1) input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.leafData
          (OriginalStructuralClassKeyDefinitions.prior p H G W).base p.window))
        (numeral 1) input parameter)) := by
  let q := OriginalTransparentDecoderValidatorCollapse.transparent p H G W
  have ht := OriginalTransparentDecoderValidatorCollapsePackedImplicationProof.sourceToTarget
    H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W input parameter hs
  have hht := iffBackward
    (OriginalStructuralKeyActivationTargetProof.targetAcceptance p H G W input parameter) ht
  have hhs := iffBackward
    (OriginalStructuralKeyActivationSourceInductionProof.sourceAcceptance p H G W input parameter) hs
  have hh := InternalAcceptanceConjunctionProof.conjunctionAccept
    (OriginalTransparentLambdaValidity.targetValidator q.base)
    (OriginalTransparentLambdaValidity.sourceValidator q.base)
    (Fin.cons input (Fin.cons parameter Fin.elim0)) hht hhs
  exact iffBackward
    (OriginalLambdaTraversalSelectionValidityProof.leafSourceCollapse q.base p.window
      body alpha Delta (numeral 1) input parameter) hh

/-- The new representative, minimum, and rank guards do not alter the decoded
source or window. The q/r difference is handled by internal validator proofs,
not by claiming their oldSource callbacks coincide. -/
theorem activeFromSource (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (input parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph
        (OriginalStructuralTraversalKey.refined p H G W P).window input parameter)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.leafData
          (OriginalStructuralTraversalKey.refined p H G W P).base
          (OriginalStructuralTraversalKey.refined p H G W P).window))
        InternalOriginalStepGuard.one input parameter))) :
    Nonempty (Derivation body Delta
      (OriginalStructuralClassKeyDefinitions.Active p H G W input parameter)) := by
  let m := OriginalStructuralTraversalKey.minimumInputs p H G W P
  have hprior : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalRankGuardedLeaf.priorData m H G W))
        InternalOriginalStepGuard.one input parameter)) := by
    have hx : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalRankGuardedLeafProof.selectedData m H G W))
        InternalOriginalStepGuard.one input parameter)) := hs
    rw [OriginalRankGuardedLeafProof.selectedValidity] at hx
    exact hx
  have hq := iffForward (OriginalRankGuardedLeafTupleProof.priorSourceIff m H G W
    InternalOriginalStepGuard.one input parameter) hprior
  have hold := oldLeafSource p H G W input parameter hq
  change Nonempty (Derivation body Delta
    (graph2 (OriginalFunctionNeutrality.active
      (OriginalLambdaTraversalSelection.transparentData
        (OriginalStructuralClassKeyDefinitions.prior p H G W).base) p.window)
      InternalOriginalStepGuard.one input parameter))
  rw [OriginalLambdaTraversalFinalGuardProof.activeLeaf]
  exact InternalAcceptanceConjunctionProof.conjunctionAccept _ _
    (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hold

theorem actualOriginalStructuralKeyActivation :
    OriginalStructuralKeyActivationTargets.ActualOriginalStructuralKeyActivation := by
  intro p H G W P body alpha Delta input parameter
  let r := OriginalStructuralTraversalKey.refined p H G W P
  let A := OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
    graph2 (InternalOriginalUniformDescentSelection.validity
      (OriginalLambdaTraversalSelection.leafData r.base r.window))
      InternalOriginalStepGuard.one input parameter
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ha⟩ := activeFromSource p H G W P input parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction ha⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationProof
