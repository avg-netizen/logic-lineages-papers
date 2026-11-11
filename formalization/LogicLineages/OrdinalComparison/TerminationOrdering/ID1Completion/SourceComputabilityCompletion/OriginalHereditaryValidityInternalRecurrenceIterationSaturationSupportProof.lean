module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof (fuelRename)
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem workRunUnique (s t m : Program 2) (left right count workCode : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (WorkRun s t m left count workCode)))
    (hr : Nonempty (Derivation body Gamma (WorkRun s t m right count workCode))) :
    Nonempty (Derivation body Gamma (eqn left right)) := by
  apply workRunCases s t m left count workCode _ hl
  intro beta j Delta state hj hs hi
  rw [eqnRelabel]
  have hr' := renameInto hr j Delta hj
  rw [workRunRename] at hr'
  exact valueUnique (iterate s t m) (left.relabel j) (right.relabel j)
    (Fin.cons (count.relabel j) (Fin.cons state Fin.elim0)) hi
    (workRunAt s t m (right.relabel j) (count.relabel j) (workCode.relabel j) state hs hr')

theorem workRunOutputTransport (s t m : Program 2) (out other count workCode : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn out other)))
    (hr : Nonempty (Derivation body Gamma (WorkRun s t m out count workCode))) :
    Nonempty (Derivation body Gamma (WorkRun s t m other count workCode)) := by
  apply workRunCases s t m out count workCode _ hr
  intro beta j Delta state hj hs hi
  rw [workRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact workRunIntro s t m (other.relabel j) (count.relabel j) (workCode.relabel j) state hs
    (outputTransport (iterate s t m) (out.relabel j) (other.relabel j)
      (Fin.cons (count.relabel j) (Fin.cons state Fin.elim0)) he' hi)

theorem successfulPadding (s t m : Program 2) (count padding workCode : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork s t m count workCode))) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m (add count padding) workCode)) :=
  terminalRunPadding s t m (numeral 2) count padding workCode hr terminalSuccess

/-- Termination at the earlier count is supplied by the separate proved
fuel theorem in the final contract. Here functionality alone removes spare
fuel, without requiring its earlier terminal endpoint to be successful. -/
theorem recoverBeforePadding (s t m : Program 2) (count padding workCode : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TerminatedWork s t m count workCode)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m (add count padding) workCode))) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m count workCode)) := by
  apply terminatedCases s t m count workCode _ ht
  intro beta j Delta out hj hr hterminal
  rw [successfulWorkRename]
  have hs' := renameInto hs j Delta hj
  simp only [successfulWorkRename,addRelabel] at hs'
  have hpadded := terminalRunPadding s t m out (count.relabel j) (padding.relabel j)
    (workCode.relabel j) hr hterminal
  have he := workRunUnique s t m out (numeral 2)
    (add (count.relabel j) (padding.relabel j)) (workCode.relabel j) hpadded hs'
  exact workRunOutputTransport s t m out (numeral 2) (count.relabel j) (workCode.relabel j) he hr

theorem acceptedAtOwnFuel (s t m : Program 2) (required workCode : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted s t m workCode))) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m required workCode)) := by
  apply acceptedCases s t m workCode _ ha
  intro beta j Delta actual hj hactual hs
  rw [successfulWorkRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have he := valueUnique workFuel actual (required.relabel j)
    (Fin.cons (workCode.relabel j) Fin.elim0) hactual hf'
  exact workRunCountTransport s t m (numeral 2) actual (required.relabel j) (workCode.relabel j) he hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
