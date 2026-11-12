module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalClassTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumCoherenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalClassProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open OriginalActiveClassKernelEqualityProof
open UniformCertificateCompletion OriginalStructuralTraversalClass
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover the actual new traversal without changing any source predicate. -/
theorem traversalPremises (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input typ parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (premises p H G W P out input typ parameter))) :
    Nonempty (Derivation body Delta
      (OriginalStructuralKeyPayloadDefinitions.premises
        (OriginalStructuralTraversalKey.refined p H G W P).base
        (OriginalStructuralTraversalKey.refined p H G W P).window out input typ parameter)) := by
  let r := OriginalStructuralTraversalKey.refined p H G W P
  obtain ⟨law⟩ := OriginalLambdaTraversalFinalCanonicalProof.actualOriginalLambdaTraversalFinalCanonical
    r body alpha Delta out input typ parameter
  obtain ⟨hp⟩ := andIntro (andLeft ha) (andLeft (andRight ha))
  obtain ⟨hf⟩ := andRight (andRight ha)
  have hc := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination law hp)) hf
  have hw := andLeft ha
  have hs := andLeft (andRight ha)
  change Nonempty (Derivation body Delta
    (OriginalFunctionNeutrality.windowGraph (OriginalLambdaTraversalSelection.finalInputs r).window input parameter)) at hw
  rw [OriginalLambdaTraversalSelectionFieldProof.finalWindow] at hw
  change Nonempty (Derivation body Delta
    (InternalParameterizedCanonicalResultFold.sourcePremises
      (OriginalLambdaTraversalSelection.finalData r) input typ parameter)) at hs
  rw [OriginalLambdaTraversalFinalPipelineIdentityProof.finalSelectedData,
    OriginalCanonicalFoldFusionFinalProof.selectedSourcePremises] at hs
  exact andIntro hw (andIntro hs ⟨hc⟩)

/-- Both target and activation of the SAME kernel are paid from actual
selected source validity. No output domain or native calibration is assumed. -/
theorem domainFromSource (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (input parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph
        (OriginalStructuralTraversalKey.refined p H G W P).window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.leafData
          (OriginalStructuralTraversalKey.refined p H G W P).base
          (OriginalStructuralTraversalKey.refined p H G W P).window)) (suc z) input parameter))) :
    Nonempty (Derivation body Delta
      (OriginalActiveClassKernel.Domain (OriginalStructuralClassKeyDefinitions.inputs p H G W)
        H G W input parameter)) := by
  let m := OriginalStructuralTraversalKey.minimumInputs p H G W P
  have hv' : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalRankGuardedLeafProof.selectedData m H G W)) (suc z) input parameter)) := hv
  rw [OriginalRankGuardedLeafProof.selectedValidity] at hv'
  obtain ⟨hi⟩ := OriginalRankGuardedLeafTupleProof.priorSourceIff
    (body := body) (Delta := Delta) m H G W (suc z) input parameter
  obtain ⟨hv'⟩ := hv'
  have hs : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G
        (InternalOriginalUniformContextMembership.contextMember p.base.member) W) (suc z) input parameter)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hi) hv'⟩
  have ht := OriginalStructuralTraversalKeyTupleProof.packedSourceToTarget H G
    (InternalOriginalUniformContextMembership.contextMember p.base.member) W input parameter hs
  have ha : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation
        (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W) (suc z) input parameter)) :=
    conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hs
  exact andIntro ht ha

theorem domains (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input typ parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (premises p H G W P out input typ parameter))) :
    Nonempty (Derivation body Delta
      (OriginalActiveClassKernel.Domain (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter ⊓
       OriginalActiveClassKernel.Domain (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W out parameter)) := by
  let r := OriginalStructuralTraversalKey.refined p H G W P
  have hp := traversalPremises p H G W P out input typ parameter ha
  have ho := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window out input typ parameter hp
  have hw := BottomDescentStepProof.windowChange r.window (suc z) input out parameter (andLeft hp)
  exact andIntro
    (domainFromSource p H G W P input parameter (andLeft hp) (andLeft (andLeft (andRight hp))))
    (domainFromSource p H G W P out parameter hw (andLeft ho))

/-- Query the old structural key inside a fresh continuation; final K
preservation supplies the candidate value in that SAME object-language scope. -/
theorem keyHit (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input typ parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (premises p H G W P out input typ parameter))) :
    Nonempty (Derivation body Delta
      (keyGraph (OriginalStructuralClassKeyDefinitions.key p H G W) input out parameter)) := by
  let K := OriginalStructuralClassKeyDefinitions.key p H G W
  apply programCases K (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hg
  rw [keyGraphRename]
  simp only [consTermRename,emptyRename] at hg
  obtain ⟨law⟩ := OriginalStructuralTraversalKeyProof.actualOriginalStructuralTraversalKeyFinal
    p H G W P body beta Theta (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) value
  have hargs : Nonempty (Derivation body Theta
      (premises p H G W P (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j))) := by
    simpa only [premises, conjunctionRename, OriginalFunctionNeutrality.windowGraph,
      OriginalVariableRepresentative.windowGraph, graph2Rename,
      InternalOriginalStepGuard.one, sucRelabel, zRelabel, sourcePremisesRename, foldGraphRename] using renameInto ha j Theta hj
  obtain ⟨hargs⟩ := hargs
  obtain ⟨hg⟩ := hg
  have ho := Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law hargs)) hg
  exact keyAccept K (input.relabel j) (out.relabel j) (parameter.relabel j) value ⟨hg⟩ ⟨ho⟩

/-- The observer's candidate-first comparison is fed actual equal rank
values; the final invariant itself is output iff input. -/
theorem rankHit (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input typ parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (premises p H G W P out input typ parameter))) :
    Nonempty (Derivation body Delta
      (observerGraph OriginalRawSyntaxTransport.variableRankPackedRaw input out parameter)) := by
  let O := OriginalRawSyntaxTransport.variableRankPackedRaw
  apply programCases O (Fin.cons input Fin.elim0) _
  intro beta j Theta value hj hg
  rw [observerGraphRename]
  simp only [consTermRename,emptyRename] at hg
  obtain ⟨law⟩ := OriginalFinalGuardedRankCompletionProof.actualOriginalFinalGuardedFoldRank
    (OriginalStructuralTraversalKey.minimumInputs p H G W P) H G W
    body beta Theta (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) value
  have hargs : Nonempty (Derivation body Theta
      (premises p H G W P (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j))) := by
    simpa only [premises, conjunctionRename, OriginalFunctionNeutrality.windowGraph,
      OriginalVariableRepresentative.windowGraph, graph2Rename,
      InternalOriginalStepGuard.one, sucRelabel, zRelabel, sourcePremisesRename, foldGraphRename]
      using renameInto ha j Theta hj
  obtain ⟨hargs⟩ := hargs
  obtain ⟨hg⟩ := hg
  have ho := Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law hargs)) hg
  exact observerAccept O (input.relabel j) (out.relabel j) (parameter.relabel j) value ⟨hg⟩ ⟨ho⟩

theorem acceptedAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input typ parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (premises p H G W P out input typ parameter))) :
    Nonempty (Derivation body Delta
      (OriginalActiveClassKernel.Accepted (OriginalStructuralClassKeyDefinitions.inputs p H G W)
        H G W OriginalRawSyntaxTransport.variableRankPackedRaw P input out parameter)) := by
  have hd := domains p H G W P out input typ parameter ha
  exact OriginalActiveClassKernelBranchProof.relationFromMatrix
    (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P input out parameter (andLeft hd)
    (andIntro (andRight hd) (andIntro
      (keyHit p H G W P out input typ parameter ha)
      (rankHit p H G W P out input typ parameter ha)))

theorem actualOriginalStructuralTraversalClassAccepted :
    OriginalStructuralTraversalClassTargets.ActualOriginalStructuralTraversalClassAccepted := by
  intro p H G W P body alpha Delta out input typ parameter
  let A := premises p H G W P out input typ parameter
  obtain ⟨answer⟩ := acceptedAt p H G W P out input typ parameter
    (body := body) (Delta := A :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction answer⟩

theorem actualOriginalStructuralTraversalClassMinimum :
    OriginalStructuralTraversalClassTargets.ActualOriginalStructuralTraversalClassMinimum := by
  intro p H G W P body alpha Delta out input typ parameter before after
  let s := OriginalStructuralClassKeyDefinitions.inputs p H G W
  let R := (OriginalActiveKernelMinimum.inputs s H G W P).base.oldRepresentative
  let A := premises p H G W P out input typ parameter ⊓
    (graph2 R before input parameter ⊓ graph2 R after out parameter)
  have ha : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨answer⟩ := OriginalActiveKernelMinimumCoherenceProof.coherenceAt s H G W P
    input out before after parameter
    (andLeft (domains p H G W P out input typ parameter (andLeft ha)))
    (acceptedAt p H G W P out input typ parameter (andLeft ha))
    (andLeft (andRight ha)) (andRight (andRight ha))
  exact ⟨Derivation.implicationIntroduction answer⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalClassProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalClassProof
