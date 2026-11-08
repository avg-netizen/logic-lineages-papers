module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionBasicProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalApplicationResultStackCompositionSyntaxProof InternalApplicationResultStackCompositionStateProof
open InternalApplicationResultStackCompositionRunProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalNumericIteration InternalNumericIterationProof InternalNumericIterationSupportProof
open InternalNumericIterationFixedPointProof InternalNumericIterationFusionProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionClosureLogicProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionFunctionalityProof
open InternalSourceInversionSupportProof InternalApplicationStepPeelSupportProof
open InternalDerivationRenamingSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem terminalValue (guard leaf : Program 1) (combine : Program 4)
    (count results state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState state results))) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationResultStack.iterate guard leaf combine) state count state)) :=
  fixedValue (InternalApplicationResultStack.transition guard leaf combine) count state
    (InternalApplicationResultStackReturnEmptyProof.emptyFixed guard leaf combine results state hs)

theorem actualOriginalResultStackTerminalIteration :
    InternalApplicationResultStackCompositionTargets.ActualOriginalResultStackTerminalIteration := by
  intro body guard leaf combine α count results state out
  let A := graph1 InternalApplicationResultStack.emptyState state results
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := InternalApplicationResultStackReturnEmptyProof.emptyFixed guard leaf combine results state h
  obtain ⟨ht⟩ := InternalNumericIterationProof.actualOriginalNumericIterationFixedPoint body
    (InternalApplicationResultStack.transition guard leaf combine) α out count state
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (weakenClosed ht [A]) hf)⟩

theorem stateEqualityRecover (state finalState work initialResults finalResults : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work initialResults)))
    (hf : Nonempty (Derivation body Gamma
      (graph1 InternalApplicationResultStack.emptyState finalState finalResults)))
    (he : Nonempty (Derivation body Gamma (eqn finalState state))) :
    Nonempty (Derivation body Gamma (eqn work z ⊓ eqn finalResults initialResults)) := by
  have hi := liveStateFields state work initialResults hs
  have ho := liveStateFields finalState z finalResults (emptyAsLive finalState finalResults hf)
  have hw := headTransport InternalApplicationResultStack.work z finalState state Fin.elim0 he (andLeft ho)
  have hr := headTransport InternalApplicationResultStack.results finalResults finalState state Fin.elim0 he (andRight ho)
  exact andIntro
    (valueUnique InternalApplicationResultStack.work work z (Fin.cons state Fin.elim0) (andLeft hi) hw)
    (valueUnique InternalApplicationResultStack.results finalResults initialResults
      (Fin.cons state Fin.elim0) hr (andRight hi))

theorem zeroRunRecover (guard leaf : Program 1) (combine : Program 4)
    (work initialResults finalResults : OTerm α)
    (h : Nonempty (Derivation body Gamma (actualRun guard leaf combine z work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (eqn work z ⊓ eqn finalResults initialResults)) := by
  apply runCases guard leaf combine z work initialResults finalResults _ h
  intro β j Delta state finalState _ hs hf ht
  simp only [conjunctionRename,eqnRelabel,zRelabel]
  simp only [zRelabel] at ht
  exact stateEqualityRecover state finalState (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) hs hf
    (repeatZeroRecover (InternalApplicationResultStack.transition guard leaf combine) finalState state ht)

theorem emptyRun (guard leaf : Program 1) (combine : Program 4) (count results : OTerm α) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine count z results results)) := by
  apply programCases InternalApplicationResultStack.emptyState (Fin.cons results Fin.elim0) _
  intro β j Delta state _ hs
  simp only [actualRunRename,zRelabel]
  simp only [consTermRename,emptyRename] at hs
  exact runIntro guard leaf combine (count.relabel j) z (results.relabel j) (results.relabel j)
    state state (emptyAsLive state (results.relabel j) hs) hs
    (terminalValue guard leaf combine (count.relabel j) (results.relabel j) state hs)

theorem zeroRunIntro (guard leaf : Program 1) (combine : Program 4)
    (work initialResults finalResults : OTerm α)
    (hw : Nonempty (Derivation body Gamma (eqn work z)))
    (hr : Nonempty (Derivation body Gamma (eqn finalResults initialResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine z work initialResults finalResults)) := by
  obtain ⟨hw⟩ := hw
  obtain ⟨hr⟩ := hr
  exact finalResultsTransport guard leaf combine z work initialResults initialResults finalResults ⟨symm hr⟩
    (workTransport guard leaf combine z z work initialResults initialResults ⟨symm hw⟩
      (emptyRun guard leaf combine z initialResults))

theorem actualOriginalResultStackRunZero :
    InternalApplicationResultStackCompositionTargets.ActualOriginalResultStackRunZero := by
  intro body guard leaf combine α work initialResults finalResults
  let P := actualRun guard leaf combine z work initialResults finalResults
  let Q := equal work z ⊓ equal finalResults initialResults
  have hf := zeroRunRecover (body := body) (Gamma := [P]) guard leaf combine work initialResults finalResults
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hq : Nonempty (Derivation body [Q] (eqn work z ⊓ eqn finalResults initialResults)) := by
    simpa only [Q,equalEqn] using (Nonempty.intro (Derivation.hypothesis (body := body) List.mem_cons_self) :
      Nonempty (Derivation body [Q] Q))
  obtain ⟨hb⟩ := zeroRunIntro guard leaf combine work initialResults finalResults (andLeft hq) (andRight hq)
  obtain ⟨hf⟩ := hf
  have hf' : Derivation body [P] Q := by simpa only [Q,equalEqn] using hf
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf') (Derivation.implicationIntroduction hb)⟩

theorem emptyRunResults (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults : OTerm α)
    (hw : Nonempty (Derivation body Gamma (eqn work z)))
    (h : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (eqn finalResults initialResults)) := by
  apply runCases guard leaf combine count work initialResults finalResults _ h
  intro β j Delta state finalState hj hs hf ht
  rw [eqnRelabel]
  have hw' := renameInto hw j Delta hj
  simp only [eqnRelabel,zRelabel] at hw'
  have he := liveAsEmpty state (initialResults.relabel j)
    (headTransport liveState state (work.relabel j) z (Fin.cons (initialResults.relabel j) Fin.elim0) hw' hs)
  have hv := terminalValue guard leaf combine (count.relabel j) (initialResults.relabel j) state he
  have heq := valueUnique (InternalApplicationResultStack.iterate guard leaf combine) finalState state
    (Fin.cons (count.relabel j) (Fin.cons state Fin.elim0)) ht hv
  exact andRight (stateEqualityRecover state finalState (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) hs hf heq)

theorem runPadding (guard leaf : Program 1) (combine : Program 4)
    (count padding work initialResults finalResults : OTerm α)
    (h : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine
      (OrdinaryArithmetic.addTerm count padding) work initialResults finalResults)) := by
  apply runCases guard leaf combine count work initialResults finalResults _ h
  intro β j Delta state finalState _ hs hf ht
  simp only [actualRunRename,InternalOriginalOrderSyntaxProof.addRelabel]
  exact runIntro guard leaf combine
    (OrdinaryArithmetic.addTerm (count.relabel j) (padding.relabel j)) (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) state finalState hs hf
    (fusionValue (InternalApplicationResultStack.transition guard leaf combine)
      (count.relabel j) (padding.relabel j) state finalState finalState ht
      (terminalValue guard leaf combine (padding.relabel j) (finalResults.relabel j) finalState hf))

theorem failureImpossible (guard leaf : Program 1) (combine : Program 4)
    (count finalState finalResults : OTerm α)
    (hf : Nonempty (Derivation body Gamma
      (graph1 InternalApplicationResultStack.emptyState finalState finalResults)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationResultStack.iterate guard leaf combine) finalState count z))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  have hz := fixedValue (body := body) (Gamma := Gamma) (InternalApplicationResultStack.transition guard leaf combine) count z
    (InternalApplicationResultStackCompositionStateProof.failureFixed guard leaf combine)
  have he := valueUnique (InternalApplicationResultStack.iterate guard leaf combine) finalState z
    (Fin.cons count (Fin.cons z Fin.elim0)) hr hz
  have hs := headTransport InternalApplicationResultStack.status (suc z) finalState z Fin.elim0 he
    (liveStatus finalState z finalResults (emptyAsLive finalState finalResults hf))
  have hzero := pairLeft (body := body) (Gamma := Gamma) (z : OTerm α) z z InternalApplicationValidityStackAppendTransitionProof.pairZero
  obtain ⟨hbad⟩ := valueUnique InternalApplicationResultStack.status (suc z) z (Fin.cons z Fin.elim0) hs hzero
  exact ⟨sucNeZeroApply hbad⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionBasicProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionBasicProof
