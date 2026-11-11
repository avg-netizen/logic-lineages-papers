module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingStateSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderStepSpecification
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalListProof
open OriginalTypedDecoderInternalBranchProof OriginalUniverseDecoderInternalNonemptyProof
open OriginalUniverseDecoderInternalSwitchProof OriginalUniverseDecoderInternalDecisionProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalAcceptanceSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Rebuild the literal live/nonempty envelope around its actual guarded step. -/
theorem transitionFromGuarded (H : Program 1) (M W : Program 2)
    (state work request rest out c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request rest)))
    (ho : Nonempty (Derivation body Delta (graph2 (guardedStep H M W) out state c))) :
    Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.transition H M W) out state c)) := by
  let xs : Fin 2 → OTerm alpha := ![state,c]
  have hstatus := pairLeftValue stateInput state (numeral 1) work xs (projectionValue 0 xs) hs
  have hwork := pairRightValue stateInput state (numeral 1) work xs (projectionValue 0 xs) hs
  have he : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]
    exact ⟨refl (numeral 1)⟩
  apply sameYesIntro stateStatus (constant 2 1) _ (constant 2 0)
    out (numeral 1) (numeral 1) xs hstatus (constantValue 1 xs) he
  exact nonzeroAtIntro stateWork (.projection 0) (guardedStep H M W) out work xs hwork
    (consNonzero work request rest hc) ho

/-- Passing the first request's source guard transports the actual typed
transition at the SAME state and SAME separate outer context. -/
theorem transitionAcceptedGuard (H : Program 1) (M W : Program 2)
    (state work request rest out c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request rest)))
    (hg : Nonempty (Derivation body Delta (guardSpec M W (numeral 1) request c)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalTypedDecoder.transition H) out state))) :
    Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.transition H M W) out state c)) := by
  let xs : Fin 2 → OTerm alpha := ![state,c]
  have hw := pairRightValue stateInput state (numeral 1) work xs (projectionValue 0 xs) hs
  have hh := headValue stateWork work request rest xs hw (consArrowFields work request rest hc)
  have hi := guardTestEquivalence M W state c request hh
  apply transitionFromGuarded H M W state work request rest out c hs hc
  apply exactOneYesIntro (guardTest M W) (oldStep H) (constant 2 0) out xs
    (impApply (andRight hi) hg)
  apply compositionValue (OriginalTypedDecoder.transition H) ![.projection 0] out xs
    (Fin.cons state Fin.elim0) ht
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 xs

/-- A rejected first-request guard constructs the literal source failure,
independently of any typed transition or successful-run premise. -/
theorem transitionRejectedGuard (H : Program 1) (M W : Program 2)
    (state work request rest c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request rest)))
    (hg : Nonempty (Derivation body Delta (guardSpec M W (numeral 1) request c).not)) :
    Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.transition H M W) z state c)) := by
  let xs : Fin 2 → OTerm alpha := ![state,c]
  have hw := pairRightValue stateInput state (numeral 1) work xs (projectionValue 0 xs) hs
  have hh := headValue stateWork work request rest xs hw (consArrowFields work request rest hc)
  have hi := guardTestEquivalence M W state c request hh
  apply transitionFromGuarded H M W state work request rest z c hs hc
  exact exactOneNoIntro (guardTest M W) (oldStep H) (constant 2 0) z xs
    (contrapose (andLeft hi) hg) (constantValue 0 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingGuardProof
