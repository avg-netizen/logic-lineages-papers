module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationWorkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationTerminalProof
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
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Reuse only the original pairing arithmetic, not the older unary
machine's transition or stack-closure theorem. -/
theorem successPair :
    Nonempty (Derivation body Gamma (StepLive (numeral 2 : OTerm alpha) z)) :=
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

theorem terminalFixed (H : Program 1) (state : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (Terminal state))) :
    Nonempty (Derivation body Gamma (graph1 (transition H) state state)) := by
  let A := eqn state z
  let B := eqn state (numeral 2)
  have ha : Derivation body (A :: Gamma) A := Derivation.hypothesis List.mem_cons_self
  have hb : Derivation body (B :: Gamma) B := Derivation.hypothesis List.mem_cons_self
  have hzero := headTransport (transition H) z z state Fin.elim0 ⟨symm ha⟩
    (failureFixed H)
  obtain ⟨da⟩ := outputTransport (transition H) z state (Fin.cons state Fin.elim0) ⟨symm ha⟩ hzero
  have hp := outputTransport InternalPairing.pairing (numeral 2) state
    (Fin.cons (numeral 1) (Fin.cons z Fin.elim0)) ⟨symm hb⟩ successPair
  obtain ⟨db⟩ := emptyFixed H state hp
  obtain ⟨ht⟩ := ht
  simp only [Terminal,equalEqn] at ht
  exact ⟨disjunctionElimination ht
    (Derivation.implicationIntroduction da) (Derivation.implicationIntroduction db)⟩

theorem iterateTerminal (H : Program 1) (count state : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (Terminal state))) :
    Nonempty (Derivation body Gamma (graph2 (iterate H) state count state)) :=
  fixedValue (transition H) count state (terminalFixed H state ht)

theorem nilSuccessful (H : Program 1) (count : OTerm alpha) :
    Nonempty (Derivation body Gamma (SuccessfulWork H count z)) :=
  workRunIntro H (numeral 2) count z (numeral 2) successPair
    (iterateEmpty H count (numeral 2) successPair)

theorem nilTerminated (H : Program 1) (count : OTerm alpha) :
    Nonempty (Derivation body Gamma (TerminatedWork H count z)) :=
  terminatedIntro H count z (numeral 2) (nilSuccessful H count) terminalSuccess

theorem rejectedWorkTerminated (H : Program 1) (count state workCode : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hf : Nonempty (Derivation body Gamma (graph1 (transition H) z state))) :
    Nonempty (Derivation body Gamma (TerminatedWork H (suc count) workCode)) :=
  terminatedIntro H (suc count) workCode z
    (workRunIntro H z (suc count) workCode state hs (rejectingFirstIterate H count state hf))
    terminalFailure

theorem continuedWorkTerminated (H : Program 1)
    (count state workCode next nextWork : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hn : Nonempty (Derivation body Gamma (StepLive next nextWork)))
    (hf : Nonempty (Derivation body Gamma (graph1 (transition H) next state)))
    (hr : Nonempty (Derivation body Gamma (TerminatedWork H count nextWork))) :
    Nonempty (Derivation body Gamma (TerminatedWork H (suc count) workCode)) := by
  apply terminatedCases H count nextWork _ hr
  intro beta j Delta out hj hi ht
  simp only [terminatedWorkRename,sucRelabel]
  have hs' := renameInto hs j Delta hj
  have hn' := renameInto hn j Delta hj
  have hf' := renameInto hf j Delta hj
  simp only [OriginalTypedDecoderInternalScalarSyntaxProof.stepLiveRename] at hs' hn'
  rw [graph1Rename] at hf'
  have hnext := workRunAt H out (count.relabel j) (nextWork.relabel j) (next.relabel j) hn' hi
  exact terminatedIntro H (suc (count.relabel j)) (workCode.relabel j) out
    (workRunIntro H out (suc (count.relabel j)) (workCode.relabel j) (state.relabel j) hs'
      (iterateAfterFirst H (count.relabel j) (state.relabel j) (next.relabel j) out hf' hnext)) ht

theorem terminatedWorkTransport (H : Program 1) (count workCode other : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn workCode other)))
    (hr : Nonempty (Derivation body Gamma (TerminatedWork H count workCode))) :
    Nonempty (Derivation body Gamma (TerminatedWork H count other)) := by
  apply terminatedCases H count workCode _ hr
  intro beta j Delta out hj hi ht
  rw [terminatedWorkRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact terminatedIntro H (count.relabel j) (other.relabel j) out
    (workRunWorkTransport H out (count.relabel j) (workCode.relabel j) (other.relabel j) he' hi) ht

theorem terminalRunPadding (H : Program 1) (out count padding workCode : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (WorkRun H out count workCode)))
    (ht : Nonempty (Derivation body Gamma (Terminal out))) :
    Nonempty (Derivation body Gamma
      (WorkRun H out (OrdinaryArithmetic.addTerm count padding) workCode)) := by
  apply workRunCases H out count workCode _ hr
  intro beta j Delta state hj hs hi
  simp only [workRunRename,InternalOriginalOrderSyntaxProof.addRelabel]
  have ht' := renameInto ht j Delta hj
  rw [terminalRename] at ht'
  exact workRunIntro H (out.relabel j)
    (OrdinaryArithmetic.addTerm (count.relabel j) (padding.relabel j)) (workCode.relabel j) state hs
    (fusionValue (transition H) (count.relabel j) (padding.relabel j) state
      (out.relabel j) (out.relabel j) hi
      (iterateTerminal H (padding.relabel j) (out.relabel j) ht'))


theorem actualOriginalTypedInternalTerminalFixed :
    OriginalTypedDecoderInternalFuelTargets.ActualOriginalTypedInternalTerminalFixed := by
  intro body H alpha out count terminal
  let A := Terminal terminal
  let P := graph2 (iterate H) out count terminal
  let Q := equal out terminal
  have ha : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hv := iterateTerminal H count terminal ha
  have hf : Nonempty (Derivation body [P,A] Q) := by
    change Nonempty (Derivation body [P,A] (equal out terminal))
    rw [equalEqn]
    exact valueUnique (iterate H) out terminal (Fin.cons count (Fin.cons terminal Fin.elim0))
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hv P)
  have hb : Nonempty (Derivation body [Q,A] P) := by
    have he : Derivation body [Q,A] (eqn out terminal) := by
      rw [← equalEqn]; exact Derivation.hypothesis List.mem_cons_self
    exact outputTransport (iterate H) terminal out (Fin.cons count (Fin.cons terminal Fin.elim0))
      ⟨symm he⟩ (withHyp hv Q)
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationTerminalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationTerminalProof
