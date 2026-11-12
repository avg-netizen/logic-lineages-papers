module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyTupleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyOtherLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open UniformCertificateCompletion OriginalStructuralTraversalKey
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalStructuralTraversalKeyOtherLeaf :
    OriginalStructuralTraversalKeyTargets.ActualOriginalStructuralTraversalKeyOtherLeaf := by
  intro p H G W P body alpha Delta out input typ parameter mark
  let m := minimumInputs p H G W P
  let r := refined p H G W P
  let D := OriginalLambdaTraversalSelection.leafData r.base r.window
  let A := OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
      (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input ⊓
        graph2 (OriginalLambdaTraversalSelection.leaf r.base r.window) out input parameter))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have supply : OriginalStructuralKeyWrapperProof.OldPreservation
      (OriginalRankGuardedLeafTupleProof.condition m H G W)
      (OriginalRankGuardedLeafTupleProof.rawData m H G W).oldRepresentative
      (OriginalStructuralClassKeyDefinitions.key p H G W) := by
    intro body alpha Delta out input parameter mark ha hr
    exact OriginalStructuralTraversalKeyTupleProof.initialKey p H G W P out input parameter mark ha hr
  obtain ⟨ho⟩ := OriginalStructuralKeyOtherLeafProof.otherKey m H G W
    (OriginalStructuralClassKeyDefinitions.key p H G W) supply out input parameter mark
    (andLeft h) (andLeft (andLeft (andRight h)))
    (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction ho⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyLeafProof
