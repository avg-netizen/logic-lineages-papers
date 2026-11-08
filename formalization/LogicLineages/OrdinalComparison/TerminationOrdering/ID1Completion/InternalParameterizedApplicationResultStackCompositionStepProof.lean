module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionBasicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalParameterizedApplicationResultStackCompositionSyntaxProof InternalApplicationResultStackCompositionStateProof
open InternalParameterizedApplicationResultStackCompositionRunProof InternalParameterizedApplicationResultStackCompositionBasicProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendRunProof (rightTransport)
open InternalNumericIteration InternalNumericIterationProof InternalNumericIterationSupportProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem runFrontForward (guard leaf : Program 2) (combine : Program 5)
    (parameter count work initialResults finalResults state nextWork nextResults nextState : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work initialResults)))
    (hn : Nonempty (Derivation body Gamma (graph2 liveState nextState nextWork nextResults)))
    (ht : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.transitionP guard leaf combine) nextState state parameter)))
    (hr : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) work initialResults finalResults))) :
    Nonempty (Derivation body Gamma
      (run guard leaf combine parameter count nextWork nextResults finalResults)) := by
  apply runCases guard leaf combine parameter (suc count) work initialResults finalResults _ hr
  intro β j Delta actual finalState hj ha hf hrun
  rw [actualRunRename]
  simp only [sucRelabel] at hrun
  have hs' := renameInto hs j Delta hj
  have hn' := renameInto hn j Delta hj
  have ht' := renameInto ht j Delta hj
  simp only [graph2Rename] at hs' hn'
  rw [graph2Rename] at ht'
  have he := valueUnique liveState actual (state.relabel j)
    (Fin.cons (work.relabel j) (Fin.cons (initialResults.relabel j) Fin.elim0)) ha hs'
  have hr' := stateTransport (InternalParameterizedApplicationResultStack.iterateP guard leaf combine)
    finalState (suc (count.relabel j)) actual (state.relabel j) (parameter.relabel j) he hrun
  exact runIntro guard leaf combine (parameter.relabel j) (count.relabel j) (nextWork.relabel j)
    (nextResults.relabel j) (finalResults.relabel j) (nextState.relabel j) finalState hn' hf
    (InternalParameterizedNumericIterationLawsProof.frontSuccForward (InternalParameterizedApplicationResultStack.transitionP guard leaf combine)
      finalState (count.relabel j) (state.relabel j) (nextState.relabel j) (parameter.relabel j) ht' hr')

theorem runFrontBackward (guard leaf : Program 2) (combine : Program 5)
    (parameter count work initialResults finalResults state nextWork nextResults nextState : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work initialResults)))
    (hn : Nonempty (Derivation body Gamma (graph2 liveState nextState nextWork nextResults)))
    (ht : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.transitionP guard leaf combine) nextState state parameter)))
    (hr : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter count nextWork nextResults finalResults))) :
    Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) work initialResults finalResults)) := by
  apply runCases guard leaf combine parameter count nextWork nextResults finalResults _ hr
  intro β j Delta actual finalState hj ha hf hrun
  simp only [actualRunRename,sucRelabel]
  have hs' := renameInto hs j Delta hj
  have hn' := renameInto hn j Delta hj
  have ht' := renameInto ht j Delta hj
  simp only [graph2Rename] at hs' hn'
  rw [graph2Rename] at ht'
  have he := valueUnique liveState actual (nextState.relabel j)
    (Fin.cons (nextWork.relabel j) (Fin.cons (nextResults.relabel j) Fin.elim0)) ha hn'
  have hr' := stateTransport (InternalParameterizedApplicationResultStack.iterateP guard leaf combine)
    finalState (count.relabel j) actual (nextState.relabel j) (parameter.relabel j) he hrun
  exact runIntro guard leaf combine (parameter.relabel j) (suc (count.relabel j)) (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) (state.relabel j) finalState hs' hf
    (InternalParameterizedNumericIterationLawsProof.frontSuccBackward (InternalParameterizedApplicationResultStack.transitionP guard leaf combine)
      finalState (count.relabel j) (state.relabel j) (nextState.relabel j) (parameter.relabel j) ht' hr')

theorem runCannotFail (guard leaf : Program 2) (combine : Program 5)
    (parameter count work initialResults finalResults state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work initialResults)))
    (ht : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.transitionP guard leaf combine) z state parameter)))
    (hr : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter (suc count) work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  apply runCases guard leaf combine parameter (suc count) work initialResults finalResults _ hr
  intro β j Delta actual finalState hj ha hf hrun
  simp only [sucRelabel] at hrun
  have hs' := renameInto hs j Delta hj
  have ht' := renameInto ht j Delta hj
  rw [graph2Rename] at hs'
  simp only [graph2Rename,zRelabel] at ht'
  have he := valueUnique liveState actual (state.relabel j)
    (Fin.cons (work.relabel j) (Fin.cons (initialResults.relabel j) Fin.elim0)) ha hs'
  have hr' := stateTransport (InternalParameterizedApplicationResultStack.iterateP guard leaf combine)
    finalState (suc (count.relabel j)) actual (state.relabel j) (parameter.relabel j) he hrun
  exact failureImpossible guard leaf combine (parameter.relabel j) (count.relabel j) finalState (finalResults.relabel j) hf
    (InternalParameterizedNumericIterationLawsProof.frontSuccForward (InternalParameterizedApplicationResultStack.transitionP guard leaf combine)
      finalState (count.relabel j) (state.relabel j) z (parameter.relabel j) ht' hr')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionStepProof
