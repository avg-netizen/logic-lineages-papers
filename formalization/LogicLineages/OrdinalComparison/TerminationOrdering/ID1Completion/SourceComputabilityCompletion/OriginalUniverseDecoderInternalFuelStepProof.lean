module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalBranchProof
open OriginalUniverseDecoderInternalNonemptyProof OriginalUniverseDecoderInternalSwitchProof
open OriginalUniverseDecoderInternalStepProof (identityBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem failureFixed (H : Program 1) (M contextWindow : Program 2) (c : OTerm alpha) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.transition H M contextWindow) z z c)) := by
  let xs : Fin 2 → OTerm alpha := ![z,c]
  have hs : Nonempty (Derivation body Delta (graph2 stateStatus z z c)) :=
    pairLeftValue stateInput z z z xs (projectionValue 0 xs)
    InternalApplicationValidityStackAppendTransitionProof.pairZero
  have hn : Nonempty (Derivation body Delta (equal (z : OTerm alpha) (numeral 1)).not) := by
    have he : Derivation body (equal (z : OTerm alpha) (numeral 1) :: Delta)
        (eqn z (suc z)) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply (symm he))⟩
  exact sameNoIntro stateStatus (constant 2 1) _ (constant 2 0) z z (numeral 1) xs
    hs (constantValue 1 xs) hn (constantValue 0 xs)

theorem emptyFixed (H : Program 1) (M contextWindow : Program 2) (state c : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepLive state z))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.transition H M contextWindow) state state c)) := by
  let xs : Fin 2 → OTerm alpha := ![state,c]
  have he : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  have hs := pairLeftValue stateInput state (numeral 1) z xs (projectionValue 0 xs) h
  have hw := pairRightValue stateInput state (numeral 1) z xs (projectionValue 0 xs) h
  apply sameYesIntro stateStatus (constant 2 1) _ (constant 2 0)
    state (numeral 1) (numeral 1) xs hs (constantValue 1 xs) he
  exact InternalAcceptanceBranchProof.zeroBranchIntro stateWork _ _ state xs hw (projectionValue 0 xs)

theorem decreaseCore (H : Program 1) (M contextWindow : Program 2)
    (state workCode previous out c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state workCode)))
    (hn : Nonempty (Derivation body Delta (equal workCode z).not))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph previous workCode)))
    (ho : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.transition H M contextWindow) out state c))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  let xs : Fin 2 → OTerm alpha := ![state,c]
  let live := InternalAcceptance.branch stateWork (.projection 0) (guardedStep H M contextWindow)
  have hstatus := pairLeftValue stateInput state (numeral 1) workCode xs (projectionValue 0 xs) hs
  have hwork := pairRightValue stateInput state (numeral 1) workCode xs (projectionValue 0 xs) hs
  have heq : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  have hlive := sameYesElim stateStatus (constant 2 1) live (constant 2 0)
    out (numeral 1) (numeral 1) xs hstatus (constantValue 1 xs) heq ho
  have hguarded := nonzeroAtElim stateWork (.projection 0) (guardedStep H M contextWindow)
    out workCode xs hwork hn hlive
  let C := graph2 (guardTest M contextWindow) (numeral 1) state c
  apply formulaCases C _
  · have hc : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hold := exactOneYesElim (guardTest M contextWindow) (oldStep H) (constant 2 0)
      out xs hc (withHyp hguarded C)
    have htyped := OriginalTypedDecoderInternalProof.fullBackward H out state
      (oldForward H out state c hold)
    exact OriginalTypedDecoderInternalFuelDecreaseProof.decreaseCore H state workCode previous out
      (withHyp hs C) (withHyp hn C) (withHyp hf C) htyped
  · have hc : Nonempty (Derivation body (C.not :: Delta) C.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hzero := exactOneNoElim (guardTest M contextWindow) (oldStep H) (constant 2 0)
      out xs hc (withHyp hguarded C.not)
    obtain ⟨he⟩ := constantForward 0 out xs hzero
    exact ⟨orLeft he⟩

theorem actualOriginalUniverseInternalWorkDecrease :
    OriginalUniverseDecoderInternalFuelTargets.ActualOriginalUniverseInternalWorkDecrease := by
  intro body H M contextWindow alpha state workCode previous out c
  let A := StepLive state workCode ⊓ ((equal workCode z).not ⊓ WorkFuelGraph previous workCode)
  let G := graph2 (OriginalUniverseDecoder.transition H M contextWindow) out state c
  have h : Nonempty (Derivation body [G,A] A) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨d⟩ := decreaseCore H M contextWindow state workCode previous out c (andLeft h)
    (andLeft (andRight h)) (andRight (andRight h)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelStepProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelStepProof.actualOriginalUniverseInternalWorkDecrease
