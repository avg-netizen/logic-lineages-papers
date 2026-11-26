module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafOtherStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion OriginalRankGuardedLeaf
open OriginalRankGuardedLeafTupleProof (rawData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def selectedData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    InternalOriginalUniformDescentSelection.Data :=
  OriginalLambdaTraversalSelection.leafData (refined p H G W).base (refined p H G W).window

theorem selectedValidity (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    InternalOriginalUniformDescentSelection.validity (selectedData p H G W) =
      InternalOriginalUniformDescentSelection.validity (priorData p H G W) :=
  OriginalApplicationSidecarIdentityProgramsProof.sameValidity (rawData p H G W) (refined p H G W).window

/-- A proof condition only. It does not replace the actual source validator
inside the transition or normalizer. -/
def otherAt : Program 2 :=
  .composition OriginalLambdaTraversalInternal.otherTag (fun _ : Fin 1 => .projection 0)

def condition (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
  InternalAcceptance.conjunction (OriginalRankGuardedLeafTupleProof.condition p H G W) otherAt

def iterationData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalGuardedObserverIteration.Data :=
  ⟨(selectedData p H G W).oldRepresentative,
    InternalOriginalUniformDescentSelection.validity (selectedData p H G W),
    condition p H G W, OriginalRawSyntaxTransport.variableRankPackedRaw⟩

theorem conditionFactors (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (input parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (condition p H G W) (suc z) input parameter))) :
    Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph (refined p H G W).window input parameter ⊓
        (graph2 (InternalOriginalUniformDescentSelection.validity (priorData p H G W))
          (suc z) input parameter ⊓
          graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hf := conjunctionRecover (OriginalRankGuardedLeafTupleProof.condition p H G W) otherAt xs ha
  have hg := OriginalRankGuardedLeafTupleProof.conditionFactors p H G W input parameter (andLeft hf)
  have ho := unaryRecover OriginalLambdaTraversalInternal.otherTag (.projection 0)
    (suc z) input xs (andRight hf) (projectionValue 0 xs)
  exact andIntro (andLeft hg) (andIntro (andRight hg) ho)

theorem conditionIntro (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (input parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph (refined p H G W).window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (priorData p H G W)) (suc z) input parameter)))
    (ho : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
    Nonempty (Derivation body Delta (graph2 (condition p H G W) (suc z) input parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hg : Nonempty (Derivation body Delta
      (graph2 (OriginalRankGuardedLeafTupleProof.condition p H G W) (suc z) input parameter)) := by
    rw [OriginalRankGuardedLeafTupleProof.conditionProgram]
    exact conjunctionAccept _ _ xs hw hv
  exact conjunctionAccept _ _ xs hg
    (unaryValue OriginalLambdaTraversalInternal.otherTag (.projection 0) (suc z) input xs ho (projectionValue 0 xs))

theorem iterationValidity (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalGuardedObserverIteration.Validity (iterationData p H G W) := by
  intro body alpha Delta input parameter ha
  change Nonempty (Derivation body Delta
    (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData p H G W)) (suc z) input parameter))
  rw [selectedValidity]
  exact andLeft (andRight (conditionFactors p H G W input parameter ha))

/-- At each real transition, paid sidecar collapse gives a prior leaf output;
its original root-shape theorem retains OTHER. Actual stepValid and unchanged
parameter pay source validity and window at that same intermediate. -/
theorem iterationClosure (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalGuardedObserverIteration.Closure (iterationData p H G W) := by
  intro body alpha Delta out input parameter ha ht
  have hf := conditionFactors p H G W input parameter ha
  have hw := andLeft hf
  have hv := andLeft (andRight hf)
  have ho := andRight (andRight hf)
  have hl := OriginalRankGuardedLeafOtherStepProof.transitionPriorLeaf
    (rawData p H G W) (refined p H G W).window out input parameter hw hv ho ht
  have hout := OriginalRankGuardedLeafOtherStepProof.priorOtherTag
    (rawData p H G W) (refined p H G W).window out input parameter hw hv hl ho
  have hv' := iterationValidity p H G W body alpha Delta input parameter ha
  have hnext := InternalParameterizedBoundedDescentNormalizerStepProof.stepValid
    (selectedData p H G W).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (selectedData p H G W)) out input parameter ht hv'
  rw [selectedValidity] at hnext
  exact conditionIntro p H G W out parameter
    (BottomDescentStepProof.windowChange (refined p H G W).window (suc z) input out parameter hw)
    hnext hout

theorem iterationPreservation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalGuardedObserverIteration.Preservation (iterationData p H G W) := by
  intro body alpha Delta out input parameter rank ha ht
  have hf := conditionFactors p H G W input parameter ha
  have hw := andLeft hf
  have hv := andLeft (andRight hf)
  have ho := andRight (andRight hf)
  have hl := OriginalRankGuardedLeafOtherStepProof.transitionPriorLeaf
    (rawData p H G W) (refined p H G W).window out input parameter hw hv ho ht
  exact OriginalRankGuardedLeafPriorProof.priorRank p H G W out input parameter rank hw hv hl

theorem otherRank (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (out input parameter rank : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph (refined p H G W).window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData p H G W)) (suc z) input parameter)))
    (ho : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input)))
    (hl : Nonempty (Derivation body Delta
      (graph2 (OriginalLambdaTraversalSelection.leaf (refined p H G W).base (refined p H G W).window)
        out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))) := by
  rw [selectedValidity] at hv
  have ha := conditionIntro p H G W input parameter hw hv ho
  exact OriginalGuardedObserverIterationSelectedProof.selectedIff (iterationData p H G W)
    (iterationValidity p H G W) (iterationClosure p H G W) (iterationPreservation p H G W)
    out input parameter rank ha hl

theorem actualOriginalRankGuardedOtherLeafRank :
    OriginalRankGuardedLeafTargets.ActualOriginalRankGuardedOtherLeafRank := by
  intro p H G W body alpha Delta out input typ parameter rank
  let A := OriginalFunctionNeutrality.windowGraph (refined p H G W).window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises (selectedData p H G W) input typ parameter ⊓
      (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input ⊓
        graph2 (OriginalLambdaTraversalSelection.leaf (refined p H G W).base (refined p H G W).window)
          out input parameter))
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := otherRank p H G W out input parameter rank
    (andLeft ha) (andLeft (andLeft (andRight ha)))
    (andLeft (andRight (andRight ha))) (andRight (andRight (andRight ha)))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafProof
