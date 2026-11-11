module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalNumericIterationProof InternalNumericIterationSupportProof
open SourceComputabilityFormulaSupportProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem successfulWorkIntro (H : Program 1) (count work state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hr : Nonempty (Derivation body Gamma (graph2 (iterate H) (numeral 2) count state))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H count work)) :=
  workRunIntro H (numeral 2) count work state hs hr

theorem successfulWorkAt (H : Program 1) (count work state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork H count work))) :
    Nonempty (Derivation body Gamma (graph2 (iterate H) (numeral 2) count state)) :=
  workRunAt H (numeral 2) count work state hs hr

theorem countTransport (H : Program 1) (count other work : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn count other)))
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H count work))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H other work)) :=
  workRunCountTransport H (numeral 2) count other work he h

theorem workTransport (H : Program 1) (count work other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn work other)))
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H count work))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H count other)) :=
  workRunWorkTransport H (numeral 2) count work other he h

theorem zeroWork (H : Program 1) (work : OTerm α)
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H z work))) :
    Nonempty (Derivation body Gamma (eqn work z)) := by
  apply workRunCases H (numeral 2) z work _ h
  intro β j Delta state _ hs hr
  simp only [eqnRelabel,zRelabel]
  simp only [zRelabel,numeral,sucRelabel,zRelabel] at hr
  obtain ⟨he⟩ := repeatZeroRecover (transition H) (numeral 2) state hr
  have hw := headTransport InternalUnpair.right (work.relabel j) state (numeral 2) Fin.elim0
    ⟨symm he⟩ (pairRight state (numeral 1) (work.relabel j) hs)
  exact valueUnique InternalUnpair.right (work.relabel j) z (Fin.cons (numeral 2) Fin.elim0)
    hw (pairRight (numeral 2) (numeral 1) z successPair)

theorem nilSuccess (H : Program 1) (count : OTerm α) :
    Nonempty (Derivation body Gamma (SuccessfulWork H count z)) :=
  OriginalTypedDecoderInternalFuelIterationTerminalProof.nilSuccessful H count

theorem successPadding (H : Program 1) (count padding work : OTerm α)
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H count work))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H (OrdinaryArithmetic.addTerm count padding) work)) :=
  OriginalTypedDecoderInternalFuelIterationSaturationSupportProof.successfulPadding H count padding work h

theorem failureImpossible (H : Program 1) (count : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 (iterate H) (numeral 2) count z))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  obtain ⟨he⟩ := valueUnique (iterate H) (numeral 2) z
    (Fin.cons count (Fin.cons z Fin.elim0)) h (iterateFailure H count)
  exact ⟨sucNeZeroApply he⟩

/-- Any successful finite original run pays acceptance at the original work
weight. Padding is justified by terminal stability, and saturation removes it. -/
theorem successfulAccepted (H : Program 1) (count work : OTerm α)
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork H count work))) :
    Nonempty (Derivation body Gamma (WorkAccepted H work)) := by
  apply programCases workFuel (Fin.cons work Fin.elim0) _
  intro β j Delta required hj hf
  rw [workAcceptedRename]
  simp only [consTermRename,emptyRename] at hf
  have hr' := renameInto hr j Delta hj
  rw [successfulWorkRename] at hr'
  exact OriginalTypedDecoderInternalFuelIterationSaturationProof.saturatedForward H
    required (OrdinaryArithmetic.addTerm (count.relabel j) required) (work.relabel j) hf
    (InternalUnpairReverseBoundsArithmeticProof.rightWeakAdd (count.relabel j) required)
    (successPadding H (count.relabel j) required (work.relabel j) hr')

theorem nilAccepted (H : Program 1) :
    Nonempty (Derivation body Gamma (WorkAccepted H (z : OTerm α))) :=
  acceptedIntro H z z OriginalTypedDecoderInternalFuelSupportProof.nilValue (nilSuccess H z)

theorem acceptedWorkTransport (H : Program 1) (work other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn work other)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H work))) :
    Nonempty (Derivation body Gamma (WorkAccepted H other)) := by
  apply acceptedCases H work _ ha
  intro β j Delta count hj hf hr
  rw [workAcceptedRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact successfulAccepted H count (other.relabel j)
    (workTransport H count (work.relabel j) (other.relabel j) he' hr)

theorem successOnePadding (H : Program 1) (count work : OTerm α)
    (h : Nonempty (Derivation body Gamma (SuccessfulWork H count work))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H (suc count) work)) := by
  have he : Derivation body Gamma (eqn (OrdinaryArithmetic.addTerm count (suc z)) (suc count)) :=
    InternalTagArithmeticSupportProof.trans (InternalTagArithmeticSupportProof.addSucc count z)
      (InternalTagArithmeticSupportProof.congSuc (InternalTagArithmeticSupportProof.addZero count))
  exact countTransport H (OrdinaryArithmetic.addTerm count (suc z)) (suc count) work ⟨he⟩
    (successPadding H count (suc z) work h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRunProof
