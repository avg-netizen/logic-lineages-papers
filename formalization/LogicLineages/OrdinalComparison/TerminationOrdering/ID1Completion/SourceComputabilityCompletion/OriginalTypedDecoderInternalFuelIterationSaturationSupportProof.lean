module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationTerminalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelSupportProof (fuelRename)
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem workRunUnique (H : Program 1) (left right count workCode : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (WorkRun H left count workCode)))
    (hr : Nonempty (Derivation body Gamma (WorkRun H right count workCode))) :
    Nonempty (Derivation body Gamma (eqn left right)) := by
  apply workRunCases H left count workCode _ hl
  intro beta j Delta state hj hs hi
  rw [eqnRelabel]
  have hr' := renameInto hr j Delta hj
  rw [workRunRename] at hr'
  exact valueUnique (iterate H) (left.relabel j) (right.relabel j)
    (Fin.cons (count.relabel j) (Fin.cons state Fin.elim0)) hi
    (workRunAt H (right.relabel j) (count.relabel j) (workCode.relabel j) state hs hr')

theorem workRunOutputTransport (H : Program 1) (out other count workCode : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn out other)))
    (hr : Nonempty (Derivation body Gamma (WorkRun H out count workCode))) :
    Nonempty (Derivation body Gamma (WorkRun H other count workCode)) := by
  apply workRunCases H out count workCode _ hr
  intro beta j Delta state hj hs hi
  rw [workRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact workRunIntro H (other.relabel j) (count.relabel j) (workCode.relabel j) state hs
    (outputTransport (iterate H) (out.relabel j) (other.relabel j)
      (Fin.cons (count.relabel j) (Fin.cons state Fin.elim0)) he' hi)

theorem successfulPadding (H : Program 1) (count padding workCode : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork H count workCode))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H (add count padding) workCode)) :=
  terminalRunPadding H (numeral 2) count padding workCode hr terminalSuccess

/-- Termination at the earlier count is supplied by the separate proved
fuel theorem in the final contract. Here functionality alone removes spare
fuel, without requiring its earlier terminal endpoint to be successful. -/
theorem recoverBeforePadding (H : Program 1) (count padding workCode : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TerminatedWork H count workCode)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H (add count padding) workCode))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H count workCode)) := by
  apply terminatedCases H count workCode _ ht
  intro beta j Delta out hj hr hterminal
  rw [successfulWorkRename]
  have hs' := renameInto hs j Delta hj
  simp only [successfulWorkRename,addRelabel] at hs'
  have hpadded := terminalRunPadding H out (count.relabel j) (padding.relabel j)
    (workCode.relabel j) hr hterminal
  have he := workRunUnique H out (numeral 2)
    (add (count.relabel j) (padding.relabel j)) (workCode.relabel j) hpadded hs'
  exact workRunOutputTransport H out (numeral 2) (count.relabel j) (workCode.relabel j) he hr

theorem acceptedAtOwnFuel (H : Program 1) (required workCode : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H workCode))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H required workCode)) := by
  apply acceptedCases H workCode _ ha
  intro beta j Delta actual hj hactual hs
  rw [successfulWorkRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have he := valueUnique workFuel actual (required.relabel j)
    (Fin.cons (workCode.relabel j) Fin.elim0) hactual hf'
  exact workRunCountTransport H (numeral 2) actual (required.relabel j) (workCode.relabel j) he hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationSupportProof
