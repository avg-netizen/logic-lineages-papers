module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationWorkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationTerminalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationTerminalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof InternalQuotientComparisonProof
open OriginalUniverseDecoderInternalFuelNumericFixedProof OriginalUniverseDecoderInternalFuelNumericFusionProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (WorkFuelGraph Terminal)
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair terminalFailure terminalSuccess)
open OriginalTypedDecoderInternalFuelIterationSyntaxProof (terminalRename)
open OriginalUniverseDecoderInternalFuelStepProof
open OriginalUniverseDecoderInternalFuelIterationProof
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalFuelIterationProof
open OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem terminalFixed (H : Program 1) (M contextWindow : Program 2) (state c : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (Terminal state))) :
    Nonempty (Derivation body Gamma (graph2 (transition H M contextWindow) state state c)) := by
  let A := eqn state z
  let B := eqn state (numeral 2)
  have ha : Derivation body (A :: Gamma) A := Derivation.hypothesis List.mem_cons_self
  have hb : Derivation body (B :: Gamma) B := Derivation.hypothesis List.mem_cons_self
  have hzero := headTransport (transition H M contextWindow) z z state ![c] ⟨symm ha⟩
    (failureFixed H M contextWindow c)
  obtain ⟨da⟩ := outputTransport (transition H M contextWindow) z state ![state,c] ⟨symm ha⟩ hzero
  have hp := outputTransport InternalPairing.pairing (numeral 2) state
    (Fin.cons (numeral 1) (Fin.cons z Fin.elim0)) ⟨symm hb⟩ successPair
  obtain ⟨db⟩ := emptyFixed H M contextWindow state c hp
  obtain ⟨ht⟩ := ht
  simp only [Terminal,equalEqn] at ht
  exact ⟨disjunctionElimination ht
    (Derivation.implicationIntroduction da) (Derivation.implicationIntroduction db)⟩

theorem iterateTerminal (H : Program 1) (M contextWindow : Program 2) (count state c : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (Terminal state))) :
    Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) state count state c)) :=
  fixedValue (transition H M contextWindow) count state c (terminalFixed H M contextWindow state c ht)

theorem nilSuccessful (H : Program 1) (M contextWindow : Program 2) (count c : OTerm alpha) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow count z c)) :=
  workRunIntro H M contextWindow (numeral 2) count z (numeral 2) c successPair
    (iterateEmpty H M contextWindow count (numeral 2) c successPair)

theorem nilTerminated (H : Program 1) (M contextWindow : Program 2) (count c : OTerm alpha) :
    Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow count z c)) :=
  terminatedIntro H M contextWindow count z (numeral 2) c (nilSuccessful H M contextWindow count c) terminalSuccess

theorem rejectedWorkTerminated (H : Program 1) (M contextWindow : Program 2) (count state workCode c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hf : Nonempty (Derivation body Gamma (graph2 (transition H M contextWindow) z state c))) :
    Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow (suc count) workCode c)) :=
  terminatedIntro H M contextWindow (suc count) workCode z c
    (workRunIntro H M contextWindow z (suc count) workCode state c hs (rejectingFirstIterate H M contextWindow count state c hf))
    terminalFailure

theorem continuedWorkTerminated (H : Program 1) (M contextWindow : Program 2)
    (count state workCode next nextWork c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hn : Nonempty (Derivation body Gamma (StepLive next nextWork)))
    (hf : Nonempty (Derivation body Gamma (graph2 (transition H M contextWindow) next state c)))
    (hr : Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow count nextWork c))) :
    Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow (suc count) workCode c)) := by
  apply terminatedCases H M contextWindow count nextWork c _ hr
  intro beta j Delta out hj hi ht
  simp only [terminatedWorkRename,sucRelabel]
  have hs' := renameInto hs j Delta hj
  have hn' := renameInto hn j Delta hj
  have hf' := renameInto hf j Delta hj
  simp only [OriginalTypedDecoderInternalScalarSyntaxProof.stepLiveRename] at hs' hn'
  rw [graph2Rename] at hf'
  have hnext := workRunAt H M contextWindow out (count.relabel j) (nextWork.relabel j) (next.relabel j) (c.relabel j) hn' hi
  exact terminatedIntro H M contextWindow (suc (count.relabel j)) (workCode.relabel j) out (c.relabel j)
    (workRunIntro H M contextWindow out (suc (count.relabel j)) (workCode.relabel j) (state.relabel j) (c.relabel j) hs'
      (iterateAfterFirst H M contextWindow (count.relabel j) (state.relabel j) (next.relabel j) out (c.relabel j) hf' hnext)) ht

theorem terminatedWorkTransport (H : Program 1) (M contextWindow : Program 2) (count workCode other c : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn workCode other)))
    (hr : Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow count workCode c))) :
    Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow count other c)) := by
  apply terminatedCases H M contextWindow count workCode c _ hr
  intro beta j Delta out hj hi ht
  rw [terminatedWorkRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact terminatedIntro H M contextWindow (count.relabel j) (other.relabel j) out (c.relabel j)
    (workRunWorkTransport H M contextWindow out (count.relabel j) (workCode.relabel j) (other.relabel j) (c.relabel j) he' hi) ht

theorem terminalRunPadding (H : Program 1) (M contextWindow : Program 2) (out count padding workCode c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count workCode c)))
    (ht : Nonempty (Derivation body Gamma (Terminal out))) :
    Nonempty (Derivation body Gamma
      (WorkRun H M contextWindow out (OrdinaryArithmetic.addTerm count padding) workCode c)) := by
  apply workRunCases H M contextWindow out count workCode c _ hr
  intro beta j Delta state hj hs hi
  simp only [workRunRename,InternalOriginalOrderSyntaxProof.addRelabel]
  have ht' := renameInto ht j Delta hj
  rw [terminalRename] at ht'
  exact workRunIntro H M contextWindow (out.relabel j)
    (OrdinaryArithmetic.addTerm (count.relabel j) (padding.relabel j)) (workCode.relabel j) state (c.relabel j) hs
    (fusionValue (transition H M contextWindow) (count.relabel j) (padding.relabel j) state
      (out.relabel j) (out.relabel j) (c.relabel j) hi
      (iterateTerminal H M contextWindow (padding.relabel j) (out.relabel j) (c.relabel j) ht'))


theorem actualOriginalUniverseInternalTerminalFixed :
    OriginalUniverseDecoderInternalFuelTargets.ActualOriginalUniverseInternalTerminalFixed := by
  intro body H M contextWindow alpha out count terminal c
  let A := Terminal terminal
  let P := graph3 (iterate H M contextWindow) out count terminal c
  let Q := equal out terminal
  have ha : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hv := iterateTerminal H M contextWindow count terminal c ha
  have hf : Nonempty (Derivation body [P,A] Q) := by
    change Nonempty (Derivation body [P,A] (equal out terminal))
    rw [equalEqn]
    exact valueUnique (iterate H M contextWindow) out terminal ![count,terminal,c]
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hv P)
  have hb : Nonempty (Derivation body [Q,A] P) := by
    have he : Derivation body [Q,A] (eqn out terminal) := by
      rw [← equalEqn]; exact Derivation.hypothesis List.mem_cons_self
    exact outputTransport (iterate H M contextWindow) terminal out ![count,terminal,c]
      ⟨symm he⟩ (withHyp hv Q)
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationTerminalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationTerminalProof
