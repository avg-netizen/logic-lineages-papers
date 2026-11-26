module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalHereditaryValidityInternalStateSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every companion code is selected by original Program totality. Pair
inverse and nonzero-list reconstruction connect those outputs to the SAME
state and current raw/parameter, without a native-calibration assumption. -/
theorem actualOriginalHereditaryLiveWorkOpening :
    OriginalHereditaryValidityInternalTargets.ActualOriginalHereditaryLiveWorkOpening := by
  intro body alpha Gamma state psi hlive k
  let qs : Fin 5 → Program 1 := ![work,currentFrame,currentRaw,currentParameter,rest]
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply queryCases qs xs psi
  intro beta j ys Delta hj hq
  apply k beta j Delta hj (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
  have hlive' := renameInto hlive j Delta hj
  rw [liveWorkRename] at hlive'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hs := reconstructPair (state.relabel j) (numeral 1) (ys 0)
    (andLeft hlive') (hq 0)
  have hh := unaryRecover InternalListCodec.headCode work (ys 1) (ys 0) xx (hq 1) (hq 0)
  have ht := unaryRecover InternalListCodec.tailCode work (ys 4) (ys 0) xx (hq 4) (hq 0)
  have hn := nonzeroOfNotZeroGraph work (ys 0) xx (hq 0) (andRight hlive')
  have hw := InternalRecursionClosureLogicProof.closedApply
    (InternalListCodecDecompositionProof.actualOriginalNonzeroListReconstruction
      body beta (ys 0) (ys 1) (ys 4)) (andIntro hn (andIntro hh ht))
  have hl := unaryRecover InternalUnpair.left currentFrame (ys 2) (ys 1) xx (hq 2) (hq 1)
  have hr := unaryRecover InternalUnpair.right currentFrame (ys 3) (ys 1) xx (hq 3) (hq 1)
  have hf := reconstructPair (ys 1) (ys 2) (ys 3) hl hr
  exact andIntro (andIntro hs (andIntro hw hf))
    (andIntro (hq 0) (andIntro (hq 1) (andIntro (hq 2) (andIntro (hq 3) (hq 4)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateProof
