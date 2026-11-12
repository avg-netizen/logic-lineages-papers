module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyMinimumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyTupleProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem packedSourceToTarget (H G : Program 1) (M W : Program 2)
    (input parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G M W) InternalOriginalStepGuard.one input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalTypedDecoder.target H G) InternalOriginalStepGuard.one input parameter)) :=
  OriginalTransparentDecoderValidatorCollapsePackedImplicationProof.sourceToTarget H G M W input parameter hs

theorem initialKey (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input parameter mark : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedLeafTupleProof.condition
        (OriginalStructuralTraversalKey.minimumInputs p H G W P) H G W)
        (suc z) input parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedLeafTupleProof.rawData
        (OriginalStructuralTraversalKey.minimumInputs p H G W P) H G W).oldRepresentative
        out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) mark out parameter).iff
        (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) mark input parameter))) := by
  have hf := OriginalRankGuardedLeafTupleProof.conditionFactors
    (OriginalStructuralTraversalKey.minimumInputs p H G W P) H G W input parameter ha
  have hs := iffForward (OriginalRankGuardedLeafTupleProof.priorSourceIff
    (OriginalStructuralTraversalKey.minimumInputs p H G W P) H G W (suc z) input parameter)
    (andRight hf)
  rw [OriginalStructuralTraversalKeyFieldsProof.source] at hs
  have ht := packedSourceToTarget H G
    (InternalOriginalUniformContextMembership.contextMember p.base.member) W input parameter hs
  have hw := andLeft hf
  change Nonempty (Derivation body Delta
    (OriginalFunctionNeutrality.windowGraph
      (OriginalStructuralTraversalKey.refined p H G W P).window input parameter)) at hw
  rw [OriginalStructuralTraversalKeyFieldsProof.window] at hw
  have hactive : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation
        (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W)
        (suc z) input parameter)) := by
    rw [OriginalStructuralTraversalKeyFieldsProof.activation]
    exact conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hs
  rw [OriginalStructuralTraversalKeyFieldsProof.rawRepresentative] at hr
  have h := OriginalStructuralTraversalKeyMinimumProof.minimumKeyIff
    (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P out input parameter mark
    (andIntro ht hactive) hr
  rw [OriginalStructuralTraversalKeyFieldsProof.representative p H G W] at h
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyTupleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyTupleProof
