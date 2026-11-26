module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalNumericIterationProof InternalNumericIterationSupportProof
open SourceComputabilityFormulaSupportProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem successfulWorkIntro (s t m : Program 2) (count work state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) work)))
    (hr : Nonempty (Derivation body Gamma (graph2 (iterate s t m) (numeral 2) count state))) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m count work)) :=
  workRunIntro s t m (numeral 2) count work state hs hr

theorem successfulWorkAt (s t m : Program 2) (count work state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) work)))
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork s t m count work))) :
    Nonempty (Derivation body Gamma (graph2 (iterate s t m) (numeral 2) count state)) :=
  workRunAt s t m (numeral 2) count work state hs hr

theorem countTransport (s t m : Program 2) (count other work : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn count other)))
    (h : Nonempty (Derivation body Gamma (SuccessfulWork s t m count work))) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m other work)) :=
  workRunCountTransport s t m (numeral 2) count other work he h

theorem workTransport (s t m : Program 2) (count work other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn work other)))
    (h : Nonempty (Derivation body Gamma (SuccessfulWork s t m count work))) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m count other)) :=
  workRunWorkTransport s t m (numeral 2) count work other he h

theorem zeroWork (s t m : Program 2) (work : OTerm α)
    (h : Nonempty (Derivation body Gamma (SuccessfulWork s t m z work))) :
    Nonempty (Derivation body Gamma (eqn work z)) := by
  apply workRunCases s t m (numeral 2) z work _ h
  intro β j Delta state _ hs hr
  simp only [eqnRelabel,zRelabel]
  simp only [zRelabel,numeral,sucRelabel,zRelabel] at hr
  obtain ⟨he⟩ := repeatZeroRecover (transition s t m) (numeral 2) state hr
  have hw := headTransport InternalUnpair.right (work.relabel j) state (numeral 2) Fin.elim0
    ⟨symm he⟩ (pairRight state (numeral 1) (work.relabel j) hs)
  exact valueUnique InternalUnpair.right (work.relabel j) z (Fin.cons (numeral 2) Fin.elim0)
    hw (pairRight (numeral 2) (numeral 1) z successPair)

theorem nilSuccess (s t m : Program 2) (count : OTerm α) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m count z)) :=
  OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof.nilSuccessful s t m count

theorem successPadding (s t m : Program 2) (count padding work : OTerm α)
    (h : Nonempty (Derivation body Gamma (SuccessfulWork s t m count work))) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m (OrdinaryArithmetic.addTerm count padding) work)) :=
  OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof.successfulPadding s t m count padding work h

theorem failureImpossible (s t m : Program 2) (count : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 (iterate s t m) (numeral 2) count z))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  obtain ⟨he⟩ := valueUnique (iterate s t m) (numeral 2) z
    (Fin.cons count (Fin.cons z Fin.elim0)) h (iterateFailure s t m count)
  exact ⟨sucNeZeroApply he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendRunProof
