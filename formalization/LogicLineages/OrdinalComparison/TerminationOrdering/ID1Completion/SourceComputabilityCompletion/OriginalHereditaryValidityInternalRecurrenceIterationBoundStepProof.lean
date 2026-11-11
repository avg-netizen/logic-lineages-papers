module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalNodeSupportProof OriginalHereditaryValidityInternalStateSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof (fuelRename withHyp)
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundCoreProof
open OriginalHereditaryValidityInternalRecurrenceIterationDecreaseProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem afterDecrease (s t m : Program 2) (count state workCode required out : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow s t m count)))
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required (suc count))))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition s t m) out state)))
    (hd : Nonempty (Derivation body Gamma (DecreasedOrFailed out required))) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m (suc count) workCode)) := by
  apply decreasedCases out required _ hd
  · intro Delta inc he
    have he' : Nonempty (Derivation body Delta (eqn out z)) := by
      simpa only [equalEqn] using he
    have hf := outputTransport (transition s t m) out z (Fin.cons state Fin.elim0)
      he' (weakenProof ht inc)
    exact rejectedWorkTerminated s t m count state workCode (weakenProof hs inc) hf
  · intro beta j Delta nextWork nextFuel hj hn hf hless
    simp only [terminatedWorkRename,sucRelabel]
    have hrow' := renameInto hrow j Delta hj
    rw [sufficientRowRename] at hrow'
    have hs' := renameInto hs j Delta hj
    simp only [StateGraph,graph2Rename,oneRename] at hs'
    have hb' := renameInto hb j Delta hj
    simp only [weakBoundRename,sucRelabel] at hb'
    have ht' := renameInto ht j Delta hj
    rw [graph1Rename] at ht'
    have hr := rowApply s t m (count.relabel j) nextWork nextFuel hrow' hf
      (decreasedBound nextFuel (required.relabel j) (count.relabel j) hless hb')
    exact continuedWorkTerminated s t m (count.relabel j) (state.relabel j)
      (workCode.relabel j) (out.relabel j) nextWork hs' hn ht' hr

theorem frameSuccessor (s t m : Program 2)
    (count state workCode frame raw parameter restCode required : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow s t m count)))
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter restCode)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required (suc count)))) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m (suc count) workCode)) := by
  apply programCases (transition s t m) (Fin.cons state Fin.elim0) _
  intro beta j Delta out hj ho
  simp only [terminatedWorkRename,sucRelabel]
  simp only [consTermRename,emptyRename] at ho
  have hrow' := renameInto hrow j Delta hj
  rw [sufficientRowRename] at hrow'
  have hs' := renameInto hs j Delta hj
  rw [stateFrameRename] at hs'
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have hb' := renameInto hb j Delta hj
  simp only [weakBoundRename,sucRelabel] at hb'
  have hd := decreaseCore s t m (state.relabel j) (workCode.relabel j) (frame.relabel j)
    (raw.relabel j) (parameter.relabel j) (restCode.relabel j) (required.relabel j) out hs' hf' ho
  exact afterDecrease s t m (count.relabel j) (state.relabel j) (workCode.relabel j)
    (required.relabel j) out hrow' (andLeft hs') hb' ho hd

theorem nonemptySuccessor (s t m : Program 2) (count state workCode required : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow s t m count)))
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) workCode)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required (suc count))))
    (hn : Nonempty (Derivation body Gamma (eqn workCode z).not)) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m (suc count) workCode)) := by
  apply OriginalHereditaryValidityInternalStateProof.actualOriginalHereditaryLiveWorkOpening
    body alpha Gamma state _ (liveFromState state workCode hs hn)
  intro beta j Delta hj actualWork frame raw parameter restCode hopen
  simp only [terminatedWorkRename,sucRelabel]
  have hrow' := renameInto hrow j Delta hj
  rw [sufficientRowRename] at hrow'
  have hs' := renameInto hs j Delta hj
  simp only [StateGraph,graph2Rename,oneRename] at hs'
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have hb' := renameInto hb j Delta hj
  simp only [weakBoundRename,sucRelabel] at hb'
  obtain ⟨he⟩ := valueUnique work actualWork (workCode.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) (andLeft (andRight hopen))
    (pairRight (state.relabel j) (numeral 1) (workCode.relabel j) hs')
  have hactual := headTransport workFuel (required.relabel j) (workCode.relabel j) actualWork
    Fin.elim0 ⟨symm he⟩ hf'
  have hr := frameSuccessor s t m (count.relabel j) (state.relabel j) actualWork
    frame raw parameter restCode (required.relabel j) hrow' (andLeft hopen) hactual hb'
  exact terminatedWorkTransport s t m (suc (count.relabel j)) actualWork (workCode.relabel j) ⟨he⟩ hr

theorem successorCore (s t m : Program 2) (count workCode required : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow s t m count)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required (suc count)))) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m (suc count) workCode)) := by
  apply InternalOriginalPairingOrderArithmeticProof.formulaCases (eqn workCode z)
  · have he : Derivation body (eqn workCode z :: Gamma) (eqn workCode z) :=
      Derivation.hypothesis List.mem_cons_self
    exact terminatedWorkTransport s t m (suc count) z workCode ⟨symm he⟩ (nilTerminated s t m (suc count))
  · let N := (eqn workCode z).not
    have hn : Nonempty (Derivation body (N :: Gamma) N) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hrowN := withHyp hrow N
    have hfN := withHyp hf N
    have hbN := withHyp hb N
    apply programCases InternalPairing.pairing (Fin.cons (numeral 1) (Fin.cons workCode Fin.elim0)) _
    intro beta j Delta state hj hs
    simp only [terminatedWorkRename,sucRelabel]
    simp only [consTermRename,emptyRename,oneRename] at hs
    have hrow' := renameInto hrowN j Delta hj
    rw [sufficientRowRename] at hrow'
    have hf' := renameInto hfN j Delta hj
    rw [fuelRename] at hf'
    have hb' := renameInto hbN j Delta hj
    simp only [weakBoundRename,sucRelabel] at hb'
    have hn' := renameInto hn j Delta hj
    change Nonempty (Derivation body Delta (((eqn workCode z).relabel j).not)) at hn'
    rw [eqnRelabel,zRelabel] at hn'
    exact nonemptySuccessor s t m (count.relabel j) state (workCode.relabel j)
      (required.relabel j) hrow' hs hf' hb' hn'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundStepProof
