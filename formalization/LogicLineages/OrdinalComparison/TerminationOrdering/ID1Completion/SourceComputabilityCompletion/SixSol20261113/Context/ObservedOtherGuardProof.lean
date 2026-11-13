module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherMarksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- The actual observer wrapper selects its original candidate when its actual
observer outputs agree. This is forward graph construction, not a new program. -/
theorem observedValue (active previous : Program 2) (observer : Program 1)
 (input output parameter mark : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph2 active (suc z) input parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 previous output input parameter)))
 (hi : Nonempty (Derivation body Delta (graph1 observer mark input)))
 (ho : Nonempty (Derivation body Delta (graph1 observer mark output))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalApplicationSidecarTransitionPipelineDefinitions.observed active observer previous) output input parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 have hc := sameAccept (.composition observer (fun _ : Fin 1 => previous))
   (.composition observer (fun _ : Fin 1 => .projection 0)) mark xs
   (unaryValue observer previous mark output xs ho hp)
   (unaryValue observer (.projection 0) mark input xs hi (projectionValue 0 xs))
 have hinner := successorBranchIntro
   (InternalApplicationStepPeel.same (.composition observer (fun _ : Fin 1 => previous))
      (.composition observer (fun _ : Fin 1 => .projection 0)))
   (.projection 0) previous output z xs hc hp
 exact successorBranchIntro active previous _ output z xs ha hinner

/-- Exact actual accepted rank graph, recovered from the old component of the
all-position relation; no supplied rank equality. -/
theorem acceptedRank (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input output parameter mark : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W input parameter)))
 (ha : Nonempty (Derivation body Delta (OriginalAllPositionMinimumCoherenceTargets.Accepted p H G W P input output parameter))) :
 Nonempty (Derivation body Delta
   ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw mark output).iff
     (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw mark input))) := by
 have hm := OriginalActiveClassKernelBranchProof.matrixFromRelation p H G W
   OriginalRawSyntaxTransport.variableRankPackedRaw P input output parameter hd
   (andLeft (OriginalAllPositionAcceptedProof.acceptedRecover p H G W P input output parameter hd ha))
 exact OriginalObservedClassProof.observerOfSame OriginalRawSyntaxTransport.variableRankPackedRaw
   mark input output parameter (andRight (andRight hm))

/-- The initial extra rank guard is genuinely discharged, not erased by a
false definitional identification of rawData with the once-minimum. -/
theorem initialValue (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input output parameter rank : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (OriginalClassContextAllPositionSelection.inputs p H G W P).base.oldRepresentative output input parameter)))
 (hi : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalRankGuardedLeafTupleProof.rawData (OriginalClassContextAllPositionSelection.inputs p H G W P) H G W).oldRepresentative
   output input parameter)) := by
 have hh := OriginalAllPositionMinimumSupportProof.minimumHit p H G W P input output parameter hd hm
 have ho := iffBackward (acceptedRank p H G W P input output parameter rank hd hh) hi
 rw [OriginalAllPositionGuardedIndexedProof.initialRepresentative]
 exact observedValue
   (OriginalRankGuardedRepresentative.active
     (OriginalTransparentDecoderSelection.transparentInputs H G W (OriginalClassContextAllPositionSelection.inputs p H G W P)).base.oldSource
     (OriginalClassContextAllPositionSelection.inputs p H G W P).window)
   (OriginalClassContextAllPositionSelection.inputs p H G W P).base.oldRepresentative
   OriginalRawSyntaxTransport.variableRankPackedRaw input output parameter rank (andRight hd) hm hi ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherGuardProof
