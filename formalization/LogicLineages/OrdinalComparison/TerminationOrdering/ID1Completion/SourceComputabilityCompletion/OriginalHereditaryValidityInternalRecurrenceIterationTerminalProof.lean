module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof InternalQuotientComparisonProof
open InternalNumericIterationFixedPointProof InternalNumericIterationFusionProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalNodeSupportProof
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Reuse only the original pairing arithmetic, not the older unary
machine's transition or stack-closure theorem. -/
theorem successPair :
    Nonempty (Derivation body Gamma (StateGraph (numeral 2 : OTerm alpha) (numeral 1) z)) :=
  InternalApplicationValidityStackAppendTransitionProof.pairOneZero

theorem terminalFailure : Nonempty (Derivation body Gamma (Terminal (z : OTerm alpha))) := by
  simpa only [Terminal,equalEqn] using
    (show Nonempty (Derivation body Gamma (eqn (z : OTerm alpha) z ⊔ eqn z (numeral 2))) from
      ⟨orLeft (refl z)⟩)

theorem terminalSuccess : Nonempty (Derivation body Gamma (Terminal (numeral 2 : OTerm alpha))) := by
  simpa only [Terminal,equalEqn] using
    (show Nonempty (Derivation body Gamma
      (eqn (numeral 2 : OTerm alpha) z ⊔ eqn (numeral 2) (numeral 2))) from
      ⟨orRight (refl (numeral 2))⟩)

theorem terminalFixed (s t m : Program 2) (state : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (Terminal state))) :
    Nonempty (Derivation body Gamma (graph1 (transition s t m) state state)) := by
  let A := eqn state z
  let B := eqn state (numeral 2)
  have ha : Derivation body (A :: Gamma) A := Derivation.hypothesis List.mem_cons_self
  have hb : Derivation body (B :: Gamma) B := Derivation.hypothesis List.mem_cons_self
  have hzero := headTransport (transition s t m) z z state Fin.elim0 ⟨symm ha⟩
    (OriginalHereditaryValidityInternalAbsorbProof.failureFixed s t m)
  obtain ⟨da⟩ := outputTransport (transition s t m) z state (Fin.cons state Fin.elim0) ⟨symm ha⟩ hzero
  have hp := outputTransport InternalPairing.pairing (numeral 2) state
    (Fin.cons (numeral 1) (Fin.cons z Fin.elim0)) ⟨symm hb⟩ successPair
  obtain ⟨db⟩ := OriginalHereditaryValidityInternalAbsorbProof.emptyFixed s t m state hp
  obtain ⟨ht⟩ := ht
  simp only [Terminal,equalEqn] at ht
  exact ⟨disjunctionElimination ht
    (Derivation.implicationIntroduction da) (Derivation.implicationIntroduction db)⟩

theorem iterateTerminal (s t m : Program 2) (count state : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (Terminal state))) :
    Nonempty (Derivation body Gamma (graph2 (iterate s t m) state count state)) :=
  fixedValue (transition s t m) count state (terminalFixed s t m state ht)

theorem nilSuccessful (s t m : Program 2) (count : OTerm alpha) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m count z)) :=
  workRunIntro s t m (numeral 2) count z (numeral 2) successPair
    (iterateEmpty s t m count (numeral 2) successPair)

theorem nilTerminated (s t m : Program 2) (count : OTerm alpha) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m count z)) :=
  terminatedIntro s t m count z (numeral 2) (nilSuccessful s t m count) terminalSuccess

theorem rejectedWorkTerminated (s t m : Program 2) (count state workCode : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) workCode)))
    (hf : Nonempty (Derivation body Gamma (graph1 (transition s t m) z state))) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m (suc count) workCode)) :=
  terminatedIntro s t m (suc count) workCode z
    (workRunIntro s t m z (suc count) workCode state hs (rejectingFirstIterate s t m count state hf))
    terminalFailure

theorem continuedWorkTerminated (s t m : Program 2)
    (count state workCode next nextWork : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) workCode)))
    (hn : Nonempty (Derivation body Gamma (StateGraph next (numeral 1) nextWork)))
    (hf : Nonempty (Derivation body Gamma (graph1 (transition s t m) next state)))
    (hr : Nonempty (Derivation body Gamma (TerminatedWork s t m count nextWork))) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m (suc count) workCode)) := by
  apply terminatedCases s t m count nextWork _ hr
  intro beta j Delta out hj hi ht
  simp only [terminatedWorkRename,sucRelabel]
  have hs' := renameInto hs j Delta hj
  have hn' := renameInto hn j Delta hj
  have hf' := renameInto hf j Delta hj
  simp only [StateGraph,graph2Rename,oneRename] at hs' hn'
  rw [graph1Rename] at hf'
  have hnext := workRunAt s t m out (count.relabel j) (nextWork.relabel j) (next.relabel j) hn' hi
  exact terminatedIntro s t m (suc (count.relabel j)) (workCode.relabel j) out
    (workRunIntro s t m out (suc (count.relabel j)) (workCode.relabel j) (state.relabel j) hs'
      (iterateAfterFirst s t m (count.relabel j) (state.relabel j) (next.relabel j) out hf' hnext)) ht

theorem terminatedWorkTransport (s t m : Program 2) (count workCode other : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn workCode other)))
    (hr : Nonempty (Derivation body Gamma (TerminatedWork s t m count workCode))) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m count other)) := by
  apply terminatedCases s t m count workCode _ hr
  intro beta j Delta out hj hi ht
  rw [terminatedWorkRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact terminatedIntro s t m (count.relabel j) (other.relabel j) out
    (workRunWorkTransport s t m out (count.relabel j) (workCode.relabel j) (other.relabel j) he' hi) ht

theorem terminalRunPadding (s t m : Program 2) (out count padding workCode : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (WorkRun s t m out count workCode)))
    (ht : Nonempty (Derivation body Gamma (Terminal out))) :
    Nonempty (Derivation body Gamma
      (WorkRun s t m out (OrdinaryArithmetic.addTerm count padding) workCode)) := by
  apply workRunCases s t m out count workCode _ hr
  intro beta j Delta state hj hs hi
  simp only [workRunRename,InternalOriginalOrderSyntaxProof.addRelabel]
  have ht' := renameInto ht j Delta hj
  rw [terminalRename] at ht'
  exact workRunIntro s t m (out.relabel j)
    (OrdinaryArithmetic.addTerm (count.relabel j) (padding.relabel j)) (workCode.relabel j) state hs
    (fusionValue (transition s t m) (count.relabel j) (padding.relabel j) state
      (out.relabel j) (out.relabel j) hi
      (iterateTerminal s t m (padding.relabel j) (out.relabel j) ht'))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof
