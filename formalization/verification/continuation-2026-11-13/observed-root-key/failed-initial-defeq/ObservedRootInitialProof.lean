module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootMinimumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionConditionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
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
  have hd := OriginalAllPositionConditionProof.conditionDomain
    (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P input parameter ha
  rw [OriginalStructuralTraversalKeyFieldSupportProof.rawRepresentative] at hr
  exact ObservedRootMinimumProof.minimumKeyIff
    (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P out input parameter mark hd hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootInitialProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootInitialProof
