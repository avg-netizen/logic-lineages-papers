module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingStateSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
open OriginalTypedDecoderInternalAcceptanceCouplingMapProof
open OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
open OriginalTypedDecoderInternalAcceptanceCouplingDispatchProof
open OriginalTypedDecoderInternalAcceptanceCouplingStateSyntaxProof

/-- Rebuild an actual original typed transition from its literal first
request and independent arithmetic mode clause. -/
theorem transitionFromMode (H : Program 1)
    (state work request rest mode gamma typ raw tag payload out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request rest)))
    (hr : Nonempty (Derivation body Delta (StepRequest request mode gamma typ raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (hm : Nonempty (Derivation body Delta (StepModeDispatch H out mode gamma typ tag payload rest))) :
    Nonempty (Derivation body Delta (graph1 (OriginalTypedDecoder.transition H) out state)) := by
  have hn := OriginalTypedDecoderInternalListProof.consNonzero work request rest hc
  have hw := OriginalTypedDecoderInternalStateSyntaxProof.nonemptyIntro H out work
    ![request,rest,mode,gamma,typ,raw,tag,payload]
    (andIntro hc (andIntro hr (andIntro hp hm)))
  have he : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]
    exact ⟨refl (numeral 1)⟩
  exact OriginalTypedDecoderInternalProof.fullBackward H out state
    (OriginalTypedDecoderInternalStateSyntaxProof.stateIntro H out state ![numeral 1,work]
      (andIntro hs (orProofRight (andIntro he (orProofRight (andIntro hn hw))))))

/-- Extract the nonempty specification from the same actual live transition. -/
theorem nonemptyAt (H : Program 1) (state workCode out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state workCode)))
    (hn : Nonempty (Derivation body Delta (eqn workCode z).not))
    (ho : Nonempty (Derivation body Delta (graph1 (OriginalTypedDecoder.transition H) out state))) :
    Nonempty (Derivation body Delta (StepNonemptyWork H out workCode)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let live := InternalAcceptance.branch OriginalTypedDecoder.work (.projection 0)
    (OriginalTypedDecoderInternalModeProof.modeProgram H)
  have hstatus := pairLeft state (numeral 1) workCode hs
  have hwork := pairRight state (numeral 1) workCode hs
  have heq : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]
    exact ⟨refl (numeral 1)⟩
  have hn' : Nonempty (Derivation body Delta (equal workCode (numeral 0)).not) := by
    simpa only [equalEqn,numeral] using hn
  have hlive := OriginalTypedDecoderInternalBranchProof.sameYesElim
    OriginalTypedDecoder.status (OriginalRawSyntaxTransport.constant 1 1) live
    (OriginalRawSyntaxTransport.constant 1 0) out (numeral 1) (numeral 1) xs
    hstatus (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xs) heq ho
  have hmode := OriginalTypedDecoderInternalBranchProof.nonzeroAtElim OriginalTypedDecoder.work (.projection 0)
    (OriginalTypedDecoderInternalModeProof.modeProgram H) out workCode xs hwork hn' hlive
  exact OriginalTypedDecoderInternalStateProof.nonemptyForward H state out workCode hwork hn' hmode

/-- Translate the already proved all-mode coupling into the two literal
transition graphs. Both sides use the identical original first request. -/
theorem requestCoupling (H : Program 1)
    (state joinedState work joinedWork request rest joinedRest mode gamma typ raw tag payload suffix out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hjs : Nonempty (Derivation body Delta (StepLive joinedState joinedWork)))
    (hc : Nonempty (Derivation body Delta (StepCons work request rest)))
    (hjc : Nonempty (Derivation body Delta (StepCons joinedWork request joinedRest)))
    (hr : Nonempty (Derivation body Delta (StepRequest request mode gamma typ raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw tag payload)))
    (hm : Nonempty (Derivation body Delta (StepModeDispatch H out mode gamma typ tag payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledStep H state joinedState suffix)) := by
  apply localCases H .modes mode gamma typ tag payload rest joinedRest suffix _
    (modeCoupling H out mode gamma typ tag payload rest joinedRest suffix hm ha)
  · intro beta j Theta hj hmode hjmode
    rw [coupledRename]
    have hs' := renameInto hs j Theta hj
    have hjs' := renameInto hjs j Theta hj
    have hc' := renameInto hc j Theta hj
    have hjc' := renameInto hjc j Theta hj
    have hr' := renameInto hr j Theta hj
    have hp' := renameInto hp j Theta hj
    simp only [stepLiveRename] at hs' hjs'
    simp only [stepConsRename] at hc' hjc'
    rw [stepRequestRename] at hr'
    rw [stepPairRename] at hp'
    exact coupledFailureIntro H _ _ _
      (transitionFromMode H _ _ _ _ _ _ _ _ _ _ z hs' hc' hr' hp' hmode)
      (transitionFromMode H _ _ _ _ _ _ _ _ _ _ z hjs' hjc' hr' hp' hjmode)
  · intro beta j Theta fw jw fs js hj happ hfs hjsf hmode hjmode
    rw [coupledRename]
    have hs' := renameInto hs j Theta hj
    have hjs' := renameInto hjs j Theta hj
    have hc' := renameInto hc j Theta hj
    have hjc' := renameInto hjc j Theta hj
    have hr' := renameInto hr j Theta hj
    have hp' := renameInto hp j Theta hj
    simp only [stepLiveRename] at hs' hjs'
    simp only [stepConsRename] at hc' hjc'
    rw [stepRequestRename] at hr'
    rw [stepPairRename] at hp'
    exact coupledLiveIntro H _ _ _ fw jw fs js
      (andIntro happ (andIntro hfs (andIntro hjsf (andIntro
        (transitionFromMode H _ _ _ _ _ _ _ _ _ _ fs hs' hc' hr' hp' hmode)
        (transitionFromMode H _ _ _ _ _ _ _ _ _ _ js hjs' hjc' hr' hp' hjmode)))))

/-- Open the literal first request and query the original append on its tail.
The unchanged suffix and all request fields are retained in both transitions. -/
theorem nonemptyCoupling (H : Program 1)
    (front suffix joined state joinedState out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hs : Nonempty (Derivation body Delta (StepLive state front)))
    (hjs : Nonempty (Derivation body Delta (StepLive joinedState joined)))
    (h : Nonempty (Derivation body Delta (StepNonemptyWork H out front))) :
    Nonempty (Derivation body Delta (CoupledStep H state joinedState suffix)) := by
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
  have hr := renameInto (andLeft (andRight fields)) k Omega hk
  have hp := renameInto (andLeft (andRight (andRight fields))) k Omega hk
  have hm := renameInto (andRight (andRight (andRight fields))) k Omega hk
  rw [stepConsRename] at hc
  rw [stepRequestRename] at hr
  rw [stepPairRename] at hp
  rw [OriginalTypedDecoderInternalDispatchSyntaxProof.stepModeDispatchRename] at hm
  have hjc := InternalApplicationValidityStackAppendListProof.consForward
    ((front.relabel j).relabel k) ((ys 0).relabel k) ((ys 1).relabel k)
    ((suffix.relabel j).relabel k) (qs 0) ((joined.relabel j).relabel k) hc (hq 0) ha''
  exact requestCoupling H _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((out.relabel j).relabel k)
    hs'' hjs'' hc hjc hr hp hm (hq 0)

/-- Totality supplies the initial actual output internally. No successful-run,
well-formed-request, or desired-next-state premise is introduced. -/
theorem frameCoupling (H : Program 1) (front suffix joined state joinedState : OTerm alpha)
    (hnz : Nonempty (Derivation body Delta (eqn front z).not))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hs : Nonempty (Derivation body Delta (StepLive state front)))
    (hjs : Nonempty (Derivation body Delta (StepLive joinedState joined))) :
    Nonempty (Derivation body Delta (CoupledStep H state joinedState suffix)) := by
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
  exact nonemptyCoupling H _ _ _ _ _ (ys 0) ha' hs' hjs'
    (nonemptyAt H _ _ (ys 0) hs' hnz' (hq 0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingStateProof
