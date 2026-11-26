module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationWorkProof OriginalTypedDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp fuelRename)
open OriginalTypedDecoderInternalFuelDecreaseSyntaxProof OriginalTypedDecoderInternalFuelDecreaseProof
open OriginalTypedDecoderInternalAcceptanceSyntaxProof OriginalTypedDecoderInternalAcceptanceRunProof
open OriginalTypedDecoderInternalAcceptanceStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem acceptedStepEmpty (H : Program 1) (state out : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state z)))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition H) out state))) :
    Nonempty (Derivation body Gamma (AcceptedState H out)) := by
  obtain ⟨he⟩ := valueUnique (transition H) out state (Fin.cons state Fin.elim0) ht
    (emptyFixed H state hs)
  exact acceptedStateIntro H out z
    (outputTransport InternalPairing.pairing state out (Fin.cons (numeral 1) (Fin.cons z Fin.elim0))
      ⟨symm he⟩ hs) (nilAccepted H)

theorem acceptedStepNonempty (H : Program 1) (state work out count : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition H) out state)))
    (hn : Nonempty (Derivation body Gamma (equal work z).not))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph count work)))
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork H count work))) :
    Nonempty (Derivation body Gamma (AcceptedState H out)) := by
  have hrun := successfulWorkAt H (suc count) work state hs (successOnePadding H count work hr)
  have hnext := iterateAfterFirstRecover H count state out (numeral 2) ht hrun
  apply decreasedCases out count _ (decreaseCore H state work count out hs hn hf ht)
  · have he : Nonempty (Derivation body (equal out z :: Gamma) (eqn out z)) := by
      rw [← equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hbad := binaryRightTransport (iterate H) (numeral 2) count out z he (withHyp hnext _)
    obtain ⟨hbot⟩ := failureImpossible H count hbad
    exact ⟨Derivation.explosion hbot⟩
  · intro beta j Delta nextWork nextFuel hj hfields
    rw [acceptedStateRename]
    have hnext' := renameInto hnext j Delta hj
    simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hnext'
    exact acceptedStateIntro H (out.relabel j) nextWork (andLeft hfields)
      (successfulAccepted H (count.relabel j) nextWork
        (successfulWorkIntro H (count.relabel j) nextWork (out.relabel j) (andLeft hfields) hnext'))

theorem acceptedStepForward (H : Program 1) (state work out : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition H) out state)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H work))) :
    Nonempty (Derivation body Gamma (AcceptedState H out)) := by
  apply InternalOriginalPairingOrderArithmeticProof.formulaCases (equal work z)
  · have he : Nonempty (Derivation body (equal work z :: Gamma) (eqn work z)) := by
      rw [← equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact acceptedStepEmpty H state out
      (binaryRightTransport InternalPairing.pairing state (numeral 1) work z he (withHyp hs _))
      (withHyp ht _)
  · let A := (equal work z).not
    have hn : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hsA := withHyp hs A
    have htA := withHyp ht A
    apply acceptedCases H work _ (withHyp ha A)
    intro beta j Delta count hj hf hr
    rw [acceptedStateRename]
    have hs' := renameInto hsA j Delta hj
    rw [stepLiveRename] at hs'
    have ht' := renameInto htA j Delta hj
    rw [graph1Rename] at ht'
    have hn' := renameInto hn j Delta hj
    change Nonempty (Derivation body Delta (((equal work z).relabel j).not)) at hn'
    simp only [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,zRelabel] at hn'
    exact acceptedStepNonempty H (state.relabel j) (work.relabel j) (out.relabel j) count
      hs' ht' hn' hf hr

theorem acceptedStepBackward (H : Program 1) (state work out : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition H) out state)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H out))) :
    Nonempty (Derivation body Gamma (WorkAccepted H work)) := by
  apply acceptedStateCases H out _ ha
  intro beta j Delta nextWork hj hn haccepted
  rw [workAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have ht' := renameInto ht j Delta hj
  rw [graph1Rename] at ht'
  apply acceptedCases H nextWork _ haccepted
  intro beta' k Theta count hk hf hr
  rw [workAcceptedRename]
  have hs'' := renameInto hs' k Theta hk
  rw [stepLiveRename] at hs''
  have ht'' := renameInto ht' k Theta hk
  rw [graph1Rename] at ht''
  have hn' := renameInto hn k Theta hk
  rw [stepLiveRename] at hn'
  have hrun := successfulWorkAt H count (nextWork.relabel k) ((out.relabel j).relabel k) hn' hr
  exact successfulAccepted H (suc count) ((work.relabel j).relabel k)
    (successfulWorkIntro H (suc count) ((work.relabel j).relabel k) ((state.relabel j).relabel k) hs''
      (iterateAfterFirst H count ((state.relabel j).relabel k) ((out.relabel j).relabel k)
        (numeral 2) ht'' hrun))

theorem actualOriginalTypedInternalAcceptedStep :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalAcceptedStep := by
  intro body H alpha state work out
  let A := StepLive state work ⊓ graph1 (transition H) out state
  let P := WorkAccepted H work
  let Q := AcceptedState H out
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := acceptedStepForward H state work out (withHyp (andLeft hh) P)
    (withHyp (andRight hh) P) (show Nonempty (Derivation body [P,A] P) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := acceptedStepBackward H state work out (withHyp (andLeft hh) Q)
    (withHyp (andRight hh) Q) (show Nonempty (Derivation body [Q,A] Q) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceStepProof
