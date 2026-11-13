module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootMinimumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootInitialProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem initialKey (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input parameter mark : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedLeafTupleProof.condition
        (OriginalAllPositionStructuralTraversalDefinitions.minimumInputs p H G W P) H G W)
        (suc z) input parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedLeafTupleProof.rawData
        (OriginalAllPositionStructuralTraversalDefinitions.minimumInputs p H G W P) H G W).oldRepresentative
        out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) mark out parameter).iff
        (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) mark input parameter))) := by
  let q := OriginalAllPositionStructuralTraversalDefinitions.minimumInputs p H G W P
  let C := OriginalRankGuardedLeafTupleProof.condition q H G W
  let K := OriginalStructuralClassKeyDefinitions.key p H G W
  have hminimum : OriginalStructuralKeyWrapperProof.OldPreservation C q.base.oldRepresentative K := by
    intro body alpha Delta out input parameter mark hc hm
    have hd := OriginalAllPositionConditionProof.conditionDomain
      (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P input parameter hc
    exact ObservedRootMinimumProof.minimumKeyIff
      (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P out input parameter mark hd hm
  have hinitial : OriginalStructuralKeyWrapperProof.OldPreservation C
      (OriginalRankGuardedLeafTupleProof.rawData q H G W).oldRepresentative K := by
    rw [OriginalAllPositionGuardedIndexedProof.initialRepresentative]
    exact OriginalStructuralKeyWrapperProof.observedPreservation C
      (OriginalRankGuardedRepresentative.active
        (OriginalTransparentDecoderSelection.transparentInputs H G W q).base.oldSource q.window)
      OriginalRawSyntaxTransport.variableRankPackedRaw q.base.oldRepresentative K hminimum
  exact hinitial body alpha Delta out input parameter mark ha hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootInitialProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootInitialProof
