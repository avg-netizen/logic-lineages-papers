module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEmptyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionBasicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionBasicProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalParameterizedApplicationResultStackCompositionSyntaxProof InternalApplicationResultStackCompositionStateProof
open InternalParameterizedApplicationResultStackCompositionRunProof
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

theorem terminalValue (guard leaf : Program 2) (combine : Program 5)
    (parameter count results state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState state results))) :
    Nonempty (Derivation body Gamma
      (graph3 (InternalParameterizedApplicationResultStack.iterateP guard leaf combine) state count state parameter)) :=
  InternalParameterizedNumericIterationLawsProof.fixedValue (InternalParameterizedApplicationResultStack.transitionP guard leaf combine) count state parameter
    (InternalParameterizedApplicationResultStackEmptyProof.emptyFixed guard leaf combine results state parameter hs)

theorem zeroRunRecover (guard leaf : Program 2) (combine : Program 5)
    (parameter work initialResults finalResults : OTerm α)
    (h : Nonempty (Derivation body Gamma (run guard leaf combine parameter z work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (eqn work z ⊓ eqn finalResults initialResults)) := by
  apply runCases guard leaf combine parameter z work initialResults finalResults _ h
  intro β j Delta state finalState _ hs hf ht
  simp only [conjunctionRename,eqnRelabel,zRelabel]
  simp only [zRelabel] at ht
  exact InternalApplicationResultStackCompositionBasicProof.stateEqualityRecover state finalState (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) hs hf
    (valueUnique (InternalParameterizedApplicationResultStack.iterateP guard leaf combine) finalState state
      (Fin.cons z (Fin.cons state (Fin.cons (parameter.relabel j) Fin.elim0))) ht
      (InternalParameterizedNumericIterationLawsProof.zeroValue
        (InternalParameterizedApplicationResultStack.transitionP guard leaf combine) state (parameter.relabel j)))

theorem emptyRun (guard leaf : Program 2) (combine : Program 5) (parameter count results : OTerm α) :
    Nonempty (Derivation body Gamma (run guard leaf combine parameter count z results results)) := by
  apply programCases InternalApplicationResultStack.emptyState (Fin.cons results Fin.elim0) _
  intro β j Delta state _ hs
  simp only [actualRunRename,zRelabel]
  simp only [consTermRename,emptyRename] at hs
  exact runIntro guard leaf combine (parameter.relabel j) (count.relabel j) z (results.relabel j) (results.relabel j)
    state state (emptyAsLive state (results.relabel j) hs) hs
    (terminalValue guard leaf combine (parameter.relabel j) (count.relabel j) (results.relabel j) state hs)

theorem zeroRunIntro (guard leaf : Program 2) (combine : Program 5)
    (parameter work initialResults finalResults : OTerm α)
    (hw : Nonempty (Derivation body Gamma (eqn work z)))
    (hr : Nonempty (Derivation body Gamma (eqn finalResults initialResults))) :
    Nonempty (Derivation body Gamma (run guard leaf combine parameter z work initialResults finalResults)) := by
  obtain ⟨hw⟩ := hw
  obtain ⟨hr⟩ := hr
  exact finalResultsTransport guard leaf combine parameter z work initialResults initialResults finalResults ⟨symm hr⟩
    (workTransport guard leaf combine parameter z z work initialResults initialResults ⟨symm hw⟩
      (emptyRun guard leaf combine parameter z initialResults))

theorem actualOriginalParameterizedResultStackRunZero :
    InternalParameterizedApplicationResultStackCompositionTargets.ActualOriginalParameterizedResultStackRunZero := by
  intro body guard leaf combine α Gamma work initialResults finalResults parameter
  let P := run guard leaf combine parameter z work initialResults finalResults
  let Q := equal work z ⊓ equal finalResults initialResults
  have hf := zeroRunRecover (body := body) (Gamma := (P :: Gamma)) guard leaf combine parameter work initialResults finalResults
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hq : Nonempty (Derivation body (Q :: Gamma) (eqn work z ⊓ eqn finalResults initialResults)) := by
    simpa only [Q,equalEqn] using (Nonempty.intro (Derivation.hypothesis (body := body) List.mem_cons_self) :
      Nonempty (Derivation body (Q :: Gamma) Q))
  obtain ⟨hb⟩ := zeroRunIntro guard leaf combine parameter work initialResults finalResults (andLeft hq) (andRight hq)
  obtain ⟨hf⟩ := hf
  have hf' : Derivation body (P :: Gamma) Q := by simpa only [Q,equalEqn] using hf
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf') (Derivation.implicationIntroduction hb)⟩

theorem emptyRunResults (guard leaf : Program 2) (combine : Program 5)
    (parameter count work initialResults finalResults : OTerm α)
    (hw : Nonempty (Derivation body Gamma (eqn work z)))
    (h : Nonempty (Derivation body Gamma (run guard leaf combine parameter count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (eqn finalResults initialResults)) := by
  apply runCases guard leaf combine parameter count work initialResults finalResults _ h
  intro β j Delta state finalState hj hs hf ht
  rw [eqnRelabel]
  have hw' := renameInto hw j Delta hj
  simp only [eqnRelabel,zRelabel] at hw'
  have he := liveAsEmpty state (initialResults.relabel j)
    (headTransport liveState state (work.relabel j) z (Fin.cons (initialResults.relabel j) Fin.elim0) hw' hs)
  have hv := terminalValue guard leaf combine (parameter.relabel j) (count.relabel j) (initialResults.relabel j) state he
  have heq := valueUnique (InternalParameterizedApplicationResultStack.iterateP guard leaf combine) finalState state
    (Fin.cons (count.relabel j) (Fin.cons state (Fin.cons (parameter.relabel j) Fin.elim0))) ht hv
  exact andRight (InternalApplicationResultStackCompositionBasicProof.stateEqualityRecover state finalState (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) hs hf heq)

theorem runPadding (guard leaf : Program 2) (combine : Program 5)
    (parameter count padding work initialResults finalResults : OTerm α)
    (h : Nonempty (Derivation body Gamma (run guard leaf combine parameter count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (run guard leaf combine parameter
      (OrdinaryArithmetic.addTerm count padding) work initialResults finalResults)) := by
  apply runCases guard leaf combine parameter count work initialResults finalResults _ h
  intro β j Delta state finalState _ hs hf ht
  simp only [actualRunRename,InternalOriginalOrderSyntaxProof.addRelabel]
  exact runIntro guard leaf combine (parameter.relabel j)
    (OrdinaryArithmetic.addTerm (count.relabel j) (padding.relabel j)) (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) state finalState hs hf
    (InternalParameterizedNumericIterationLawsProof.fusionValue (InternalParameterizedApplicationResultStack.transitionP guard leaf combine)
      finalState (count.relabel j) (padding.relabel j) state finalState (parameter.relabel j) ht
      (terminalValue guard leaf combine (parameter.relabel j) (padding.relabel j) (finalResults.relabel j) finalState hf))


/-- Original failure remains absorbing at the same symbolic parameter. -/
theorem failureFixed (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.transitionP guard leaf combine) z z parameter)) := by
  let ss : Fin 1 → OTerm α := Fin.cons z Fin.elim0
  let xs : Fin 2 → OTerm α := Fin.cons z (Fin.cons parameter Fin.elim0)
  have hs : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.status (z : OTerm α) z)) :=
    pairLeft z z z InternalApplicationValidityStackAppendTransitionProof.pairZero
  have he := InternalEqualityTestCompositionProof.rejectForwardGap (body := body) (Gamma := Gamma)
    (z : OTerm α) (suc z) z ⟨InternalAdditionLawsProof.leftZero (suc z)⟩
  apply InternalAcceptanceBranchProof.zeroBranchIntro _ _ _ z xs
  · apply InternalParameterizedApplicationResultStackWiringProof.liftValue _ z z parameter
    exact binaryValue InternalEqualityTest.equalityTest InternalApplicationResultStack.status
      (InternalLessThan.constantOne 1) z z (suc z) ss he hs
      (InternalLessThanSupportProof.oneConstantValue ss)
  · exact InternalAcceptanceConjunctionProof.constantZeroValue xs

theorem failureImpossible (guard leaf : Program 2) (combine : Program 5)
    (parameter count finalState finalResults : OTerm α)
    (hf : Nonempty (Derivation body Gamma
      (graph1 InternalApplicationResultStack.emptyState finalState finalResults)))
    (hr : Nonempty (Derivation body Gamma
      (graph3 (InternalParameterizedApplicationResultStack.iterateP guard leaf combine) finalState count z parameter))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  have hz := InternalParameterizedNumericIterationLawsProof.fixedValue (body := body) (Gamma := Gamma)
    (InternalParameterizedApplicationResultStack.transitionP guard leaf combine) count z parameter
    (failureFixed guard leaf combine parameter)
  have he := valueUnique (InternalParameterizedApplicationResultStack.iterateP guard leaf combine) finalState z
    (Fin.cons count (Fin.cons z (Fin.cons parameter Fin.elim0))) hr hz
  have hs := headTransport InternalApplicationResultStack.status (suc z) finalState z Fin.elim0 he
    (liveStatus finalState z finalResults (emptyAsLive finalState finalResults hf))
  have hzero := pairLeft (body := body) (Gamma := Gamma) (z : OTerm α) z z InternalApplicationValidityStackAppendTransitionProof.pairZero
  obtain ⟨hbad⟩ := valueUnique InternalApplicationResultStack.status (suc z) z (Fin.cons z Fin.elim0) hs hzero
  exact ⟨sucNeZeroApply hbad⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionBasicProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionBasicProof
