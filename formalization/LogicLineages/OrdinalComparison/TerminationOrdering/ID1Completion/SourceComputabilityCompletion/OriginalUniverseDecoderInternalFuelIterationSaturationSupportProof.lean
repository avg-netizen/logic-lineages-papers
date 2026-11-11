module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationTerminalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (workFuel WorkFuelGraph Terminal)
open OriginalTypedDecoderInternalFuelSupportProof (fuelRename)
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalUniverseDecoderInternalFuelIterationTerminalProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (terminalSuccess)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem workRunUnique (H : Program 1) (M contextWindow : Program 2) (left right count workCode c : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (WorkRun H M contextWindow left count workCode c)))
    (hr : Nonempty (Derivation body Gamma (WorkRun H M contextWindow right count workCode c))) :
    Nonempty (Derivation body Gamma (eqn left right)) := by
  apply workRunCases H M contextWindow left count workCode c _ hl
  intro beta j Delta state hj hs hi
  rw [eqnRelabel]
  have hr' := renameInto hr j Delta hj
  rw [workRunRename] at hr'
  exact valueUnique (iterate H M contextWindow) (left.relabel j) (right.relabel j)
    ![count.relabel j,state,c.relabel j] hi
    (workRunAt H M contextWindow (right.relabel j) (count.relabel j) (workCode.relabel j) state (c.relabel j) hs hr')

theorem workRunOutputTransport (H : Program 1) (M contextWindow : Program 2) (out other count workCode c : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn out other)))
    (hr : Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count workCode c))) :
    Nonempty (Derivation body Gamma (WorkRun H M contextWindow other count workCode c)) := by
  apply workRunCases H M contextWindow out count workCode c _ hr
  intro beta j Delta state hj hs hi
  rw [workRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact workRunIntro H M contextWindow (other.relabel j) (count.relabel j) (workCode.relabel j) state (c.relabel j) hs
    (outputTransport (iterate H M contextWindow) (out.relabel j) (other.relabel j)
      ![count.relabel j,state,c.relabel j] he' hi)

theorem successfulPadding (H : Program 1) (M contextWindow : Program 2) (count padding workCode c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow count workCode c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow (add count padding) workCode c)) :=
  terminalRunPadding H M contextWindow (numeral 2) count padding workCode c hr terminalSuccess

/-- Termination at the earlier count is supplied by the separate proved
fuel theorem in the final contract. Here functionality alone removes spare
fuel, without requiring its earlier terminal endpoint to be successful. -/
theorem recoverBeforePadding (H : Program 1) (M contextWindow : Program 2) (count padding workCode c : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow count workCode c)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow (add count padding) workCode c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow count workCode c)) := by
  apply terminatedCases H M contextWindow count workCode c _ ht
  intro beta j Delta out hj hr hterminal
  rw [successfulWorkRename]
  have hs' := renameInto hs j Delta hj
  simp only [successfulWorkRename,addRelabel] at hs'
  have hpadded := terminalRunPadding H M contextWindow out (count.relabel j) (padding.relabel j)
    (workCode.relabel j) (c.relabel j) hr hterminal
  have he := workRunUnique H M contextWindow out (numeral 2)
    (add (count.relabel j) (padding.relabel j)) (workCode.relabel j) (c.relabel j) hpadded hs'
  exact workRunOutputTransport H M contextWindow out (numeral 2) (count.relabel j) (workCode.relabel j) (c.relabel j) he hr

theorem acceptedAtOwnFuel (H : Program 1) (M contextWindow : Program 2) (required workCode c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H M contextWindow workCode c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow required workCode c)) := by
  apply acceptedCases H M contextWindow workCode c _ ha
  intro beta j Delta actual hj hactual hs
  rw [successfulWorkRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have he := valueUnique workFuel actual (required.relabel j)
    (Fin.cons (workCode.relabel j) Fin.elim0) hactual hf'
  exact workRunCountTransport H M contextWindow (numeral 2) actual (required.relabel j) (workCode.relabel j) (c.relabel j) he hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationSupportProof
