module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePaidStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (WorkFuelGraph)
open OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalFuelIterationWorkProof OriginalUniverseDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationWorkProof (binaryRightTransport)
open OriginalTypedDecoderInternalFuelSupportProof (withHyp fuelRename)
open OriginalTypedDecoderInternalFuelDecreaseSyntaxProof
open OriginalUniverseDecoderInternalFuelStepProof
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof OriginalUniverseDecoderInternalAcceptanceRunProof
open OriginalUniverseDecoderInternalAcceptanceStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem acceptedStepEmpty (H : Program 1) (M W : Program 2) (state out c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state z)))
    (ht : Nonempty (Derivation body Gamma (graph2 (transition H M W) out state c))) :
    Nonempty (Derivation body Gamma (AcceptedState H M W out c)) := by
  obtain ⟨he⟩ := valueUnique (transition H M W) out state ![state,c] ht
    (emptyFixed H M W state c hs)
  exact acceptedStateIntro H M W out z c
    (outputTransport InternalPairing.pairing state out (Fin.cons (numeral 1) (Fin.cons z Fin.elim0))
      ⟨symm he⟩ hs) (nilAccepted H M W c)

theorem acceptedStepNonempty (H : Program 1) (M W : Program 2) (state work out count c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (ht : Nonempty (Derivation body Gamma (graph2 (transition H M W) out state c)))
    (hn : Nonempty (Derivation body Gamma (equal work z).not))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph count work)))
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork H M W count work c))) :
    Nonempty (Derivation body Gamma (AcceptedState H M W out c)) := by
  have hrun := successfulWorkAt H M W (suc count) work state c hs (successOnePadding H M W count work c hr)
  have hnext := iterateAfterFirstRecover H M W count state out (numeral 2) c ht hrun
  apply decreasedCases out count _ (decreaseCore H M W state work count out c hs hn hf ht)
  · have he : Nonempty (Derivation body (equal out z :: Gamma) (eqn out z)) := by
      rw [← equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hbad := ternaryMiddleTransport (iterate H M W) (numeral 2) count out z c he (withHyp hnext _)
    obtain ⟨hbot⟩ := failureImpossible H M W count c hbad
    exact ⟨Derivation.explosion hbot⟩
  · intro beta j Delta nextWork nextFuel hj hfields
    rw [acceptedStateRename]
    have hnext' := renameInto hnext j Delta hj
    simp only [graph3Rename,numeral,sucRelabel,zRelabel] at hnext'
    exact acceptedStateIntro H M W (out.relabel j) nextWork (c.relabel j) (andLeft hfields)
      (successfulAccepted H M W (count.relabel j) nextWork (c.relabel j)
        (successfulWorkIntro H M W (count.relabel j) nextWork (out.relabel j) (c.relabel j) (andLeft hfields) hnext'))

theorem acceptedStepForward (H : Program 1) (M W : Program 2) (state work out c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (ht : Nonempty (Derivation body Gamma (graph2 (transition H M W) out state c)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H M W work c))) :
    Nonempty (Derivation body Gamma (AcceptedState H M W out c)) := by
  apply InternalOriginalPairingOrderArithmeticProof.formulaCases (equal work z)
  · have he : Nonempty (Derivation body (equal work z :: Gamma) (eqn work z)) := by
      rw [← equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact acceptedStepEmpty H M W state out c
      (binaryRightTransport InternalPairing.pairing state (numeral 1) work z he (withHyp hs _))
      (withHyp ht _)
  · let A := (equal work z).not
    have hn : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hsA := withHyp hs A
    have htA := withHyp ht A
    apply acceptedCases H M W work c _ (withHyp ha A)
    intro beta j Delta count hj hf hr
    rw [acceptedStateRename]
    have hs' := renameInto hsA j Delta hj
    rw [stepLiveRename] at hs'
    have ht' := renameInto htA j Delta hj
    rw [graph2Rename] at ht'
    have hn' := renameInto hn j Delta hj
    change Nonempty (Derivation body Delta (((equal work z).relabel j).not)) at hn'
    simp only [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,zRelabel] at hn'
    exact acceptedStepNonempty H M W (state.relabel j) (work.relabel j) (out.relabel j) count (c.relabel j)
      hs' ht' hn' hf hr

theorem acceptedStepBackward (H : Program 1) (M W : Program 2) (state work out c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (ht : Nonempty (Derivation body Gamma (graph2 (transition H M W) out state c)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W work c)) := by
  apply acceptedStateCases H M W out c _ ha
  intro beta j Delta nextWork hj hn haccepted
  rw [workAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have ht' := renameInto ht j Delta hj
  rw [graph2Rename] at ht'
  apply acceptedCases H M W nextWork (c.relabel j) _ haccepted
  intro beta' k Theta count hk hf hr
  rw [workAcceptedRename]
  have hs'' := renameInto hs' k Theta hk
  rw [stepLiveRename] at hs''
  have ht'' := renameInto ht' k Theta hk
  rw [graph2Rename] at ht''
  have hn' := renameInto hn k Theta hk
  rw [stepLiveRename] at hn'
  have hrun := successfulWorkAt H M W count (nextWork.relabel k) ((out.relabel j).relabel k) ((c.relabel j).relabel k) hn' hr
  exact successfulAccepted H M W (suc count) ((work.relabel j).relabel k) ((c.relabel j).relabel k)
    (successfulWorkIntro H M W (suc count) ((work.relabel j).relabel k) ((state.relabel j).relabel k) ((c.relabel j).relabel k) hs''
      (iterateAfterFirst H M W count ((state.relabel j).relabel k) ((out.relabel j).relabel k)
        (numeral 2) ((c.relabel j).relabel k) ht'' hrun))

theorem actualOriginalUniverseInternalAcceptedStep :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalAcceptedStep := by
  intro body H M W alpha state work out c
  let A := StepLive state work ⊓ graph2 (transition H M W) out state c
  let P := WorkAccepted H M W work c
  let Q := AcceptedState H M W out c
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := acceptedStepForward H M W state work out c (withHyp (andLeft hh) P)
    (withHyp (andRight hh) P) (show Nonempty (Derivation body [P,A] P) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := acceptedStepBackward H M W state work out c (withHyp (andLeft hh) Q)
    (withHyp (andRight hh) Q) (show Nonempty (Derivation body [Q,A] Q) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePaidStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePaidStepProof
