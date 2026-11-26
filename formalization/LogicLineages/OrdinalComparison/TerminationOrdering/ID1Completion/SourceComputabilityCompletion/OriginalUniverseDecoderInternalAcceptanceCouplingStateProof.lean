module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalUniverseDecoderInternalSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceCouplingStateSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceCouplingGuardProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Both live states contain exactly the same first request, so the same
source guard decides both transitions. Typed suffix coupling is used only
inside its internally proved passing-guard branch. -/
theorem requestCoupling (H : Program 1) (M W : Program 2)
    (state joinedState work joinedWork request rest joinedRest suffix c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hjs : Nonempty (Derivation body Delta (StepLive joinedState joinedWork)))
    (hc : Nonempty (Derivation body Delta (StepCons work request rest)))
    (hjc : Nonempty (Derivation body Delta (StepCons joinedWork request joinedRest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedWork work suffix))) :
    Nonempty (Derivation body Delta (CoupledStep H M W state joinedState suffix c)) := by
  let C := guardSpec M W (numeral 1) request c
  apply formulaCases C _
  · have hg : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hsC := withHyp hs C
    have hjsC := withHyp hjs C
    have hcC := withHyp hc C
    have hjcC := withHyp hjc C
    have hn : Nonempty (Derivation body (C :: Delta) (eqn work z).not) := by
      simpa only [equalEqn,numeral] using
        OriginalTypedDecoderInternalListProof.consNonzero work request rest hcC
    apply OriginalTypedDecoderInternalAcceptanceCouplingFrameProof.frameCases
      H work suffix joinedWork state joinedState _ hn (withHyp ha C) hsC hjsC
    · intro beta j Theta hj ht hjt
      rw [coupledRename]
      have hs' := renameInto hsC j Theta hj
      have hjs' := renameInto hjsC j Theta hj
      have hc' := renameInto hcC j Theta hj
      have hjc' := renameInto hjcC j Theta hj
      have hg' := renameInto hg j Theta hj
      simp only [stepLiveRename] at hs' hjs'
      simp only [stepConsRename] at hc' hjc'
      change Nonempty (Derivation body Theta ((guardSpec M W (numeral 1) request c).relabel j)) at hg'
      simp only [guardRename,numeral,sucRelabel,zRelabel] at hg'
      exact coupledFailureIntro H M W _ _ _ _
        (transitionAcceptedGuard H M W _ _ _ _ z _ hs' hc' hg' ht)
        (transitionAcceptedGuard H M W _ _ _ _ z _ hjs' hjc' hg' hjt)
    · intro beta j Theta fw jw fs js hj happ hfs hjsf ht hjt
      rw [coupledRename]
      have hs' := renameInto hsC j Theta hj
      have hjs' := renameInto hjsC j Theta hj
      have hc' := renameInto hcC j Theta hj
      have hjc' := renameInto hjcC j Theta hj
      have hg' := renameInto hg j Theta hj
      simp only [stepLiveRename] at hs' hjs'
      simp only [stepConsRename] at hc' hjc'
      change Nonempty (Derivation body Theta ((guardSpec M W (numeral 1) request c).relabel j)) at hg'
      simp only [guardRename,numeral,sucRelabel,zRelabel] at hg'
      exact coupledLiveIntro H M W _ _ _ _ fw jw fs js
        (andIntro happ (andIntro hfs (andIntro hjsf (andIntro
          (transitionAcceptedGuard H M W _ _ _ _ fs _ hs' hc' hg' ht)
          (transitionAcceptedGuard H M W _ _ _ _ js _ hjs' hjc' hg' hjt)))))
  · have hg : Nonempty (Derivation body (C.not :: Delta) C.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact coupledFailureIntro H M W state joinedState suffix c
      (transitionRejectedGuard H M W state work request rest c
        (withHyp hs C.not) (withHyp hc C.not) hg)
      (transitionRejectedGuard H M W joinedState joinedWork request joinedRest c
        (withHyp hjs C.not) (withHyp hjc C.not) hg)

/-- Open the literal front request and append its tail to the unchanged suffix.
The original append law supplies the SAME first request in the joined work. -/
theorem nonemptyCoupling (H : Program 1) (M W : Program 2)
    (front suffix joined state joinedState c out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hs : Nonempty (Derivation body Delta (StepLive state front)))
    (hjs : Nonempty (Derivation body Delta (StepLive joinedState joined)))
    (h : Nonempty (Derivation body Delta (StepNonemptyWork H out front))) :
    Nonempty (Derivation body Delta (CoupledStep H M W state joinedState suffix c)) := by
  apply OriginalTypedDecoderInternalStateSyntaxProof.nonemptyCases H out front _ h
  intro beta j Theta ys hj fields
  rw [coupledRename]
  have ha' := renameInto ha j Theta hj
  have hs' := renameInto hs j Theta hj
  have hjs' := renameInto hjs j Theta hj
  rw [graph2Rename] at ha'
  simp only [stepLiveRename] at hs' hjs'
  apply queryCases (![InternalApplicationValidityStackAppend.append] : Fin 1 → Program 2)
    (Fin.cons (ys 1) (Fin.cons (suffix.relabel j) Fin.elim0)) _
  intro chi k qs Omega hk hq
  rw [coupledRename]
  simp only [consTermRename,emptyRename] at hq
  have ha'' := renameInto ha' k Omega hk
  have hs'' := renameInto hs' k Omega hk
  have hjs'' := renameInto hjs' k Omega hk
  rw [graph2Rename] at ha''
  simp only [stepLiveRename] at hs'' hjs''
  have hc := renameInto (andLeft fields) k Omega hk
  rw [stepConsRename] at hc
  have hjc := InternalApplicationValidityStackAppendListProof.consForward
    ((front.relabel j).relabel k) ((ys 0).relabel k) ((ys 1).relabel k)
    ((suffix.relabel j).relabel k) (qs 0) ((joined.relabel j).relabel k) hc (hq 0) ha''
  exact requestCoupling H M W
    ((state.relabel j).relabel k) ((joinedState.relabel j).relabel k)
    ((front.relabel j).relabel k) ((joined.relabel j).relabel k)
    ((ys 0).relabel k) ((ys 1).relabel k) (qs 0)
    ((suffix.relabel j).relabel k) ((c.relabel j).relabel k) hs'' hjs'' hc hjc ha''

/-- Internal totality supplies a typed output solely to expose its first
request. The guarded source outputs are then constructed independently. -/
theorem frameCoupling (H : Program 1) (M W : Program 2)
    (front suffix joined state joinedState c : OTerm alpha)
    (hnz : Nonempty (Derivation body Delta (eqn front z).not))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hs : Nonempty (Derivation body Delta (StepLive state front)))
    (hjs : Nonempty (Derivation body Delta (StepLive joinedState joined))) :
    Nonempty (Derivation body Delta (CoupledStep H M W state joinedState suffix c)) := by
  apply queryCases (![OriginalTypedDecoder.transition H] : Fin 1 → Program 1)
    (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [coupledRename]
  simp only [consTermRename,emptyRename] at hq
  have hnz' := renameInto hnz j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnz'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hs' := renameInto hs j Theta hj
  have hjs' := renameInto hjs j Theta hj
  simp only [stepLiveRename] at hs' hjs'
  exact nonemptyCoupling H M W _ _ _ _ _ _ (ys 0) ha' hs' hjs'
    (OriginalTypedDecoderInternalAcceptanceCouplingStateProof.nonemptyAt H _ _ (ys 0) hs' hnz' (hq 0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingStateProof
