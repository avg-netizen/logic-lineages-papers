module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackCompositionStateProof InternalParameterizedApplicationResultStackEmptyProof
open InternalApplicationResultStackCompositionFrameSupportProof (extend identityExtend identityExtendRecover)
open InternalParameterizedApplicationResultStackCompositionFrameCoreProof
open InternalParameterizedApplicationResultStackCompositionFrameQueryProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalApplicationValidityStackAppendRunProof (rightTransport)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
open InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalParameterizedApplicationResultStack
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Existentially expose only actual Program outputs; all machine branches
are handled inside the original calculus by atQueries. -/
theorem nonemptyFrameCases (mw mr : Bool) (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (stack results workBackground resultBackground framedStack framedResults state framedState : OTerm α)
    (psi : Formula α)
    (hn : Nonempty (Derivation body Gamma (eqn stack z).not))
    (hw : Nonempty (Derivation body Gamma (graph2 (extend mw) framedStack stack workBackground)))
    (hr : Nonempty (Derivation body Gamma (graph2 (extend mr) framedResults results resultBackground)))
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hfs : Nonempty (Derivation body Gamma (graph2 liveState framedState framedStack framedResults)))
    (kfail : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) z (state.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j)))
    (klive : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (nextWork framedNextWork nextResults framedNextResults nextState framedNextState : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 (extend mw) framedNextWork nextWork (workBackground.relabel j))) →
      Nonempty (Derivation body Delta (graph2 (extend mr) framedNextResults nextResults (resultBackground.relabel j))) →
      Nonempty (Derivation body Delta (graph2 liveState nextState nextWork nextResults)) →
      Nonempty (Derivation body Delta (graph2 liveState framedNextState framedNextWork framedNextResults)) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) nextState (state.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) framedNextState (framedState.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply queryCases (queries mw mr leaf combine)
    (Fin.cons stack (Fin.cons results (Fin.cons workBackground (Fin.cons resultBackground
      (Fin.cons framedStack (Fin.cons framedResults (Fin.cons parameter Fin.elim0))))))) psi
  intro β j ys Delta hj hq
  have hn' := renameInto hn j Delta hj
  have hw' := renameInto hw j Delta hj
  have hr' := renameInto hr j Delta hj
  have hs' := renameInto hs j Delta hj
  have hfs' := renameInto hfs j Delta hj
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  simp only [graph2Rename] at hw' hr' hs' hfs'
  simp only [consTermRename,emptyRename] at hq
  apply atQueries mw mr guard leaf combine (parameter.relabel j) (stack.relabel j) (results.relabel j)
    (workBackground.relabel j) (resultBackground.relabel j) (framedStack.relabel j)
    (framedResults.relabel j) (state.relabel j) (framedState.relabel j)
    ys (psi.relabel j) hn' hw' hr' hs' hfs' hq
  · intro Theta inc hf
    exact kfail β j Theta (fun p hp => inc _ (hj p hp)) hf
  · intro Theta nextWork framedNextWork nextResults framedNextResults nextState framedNextState inc hw hr hs hfs ht hft
    exact klive β j Theta nextWork framedNextWork nextResults framedNextResults nextState framedNextState
      (fun p hp => inc _ (hj p hp)) hw hr hs hfs ht hft

/-- Nonempty work prefix simulation with the exact unchanged result stack.
Failure is exposed only for the original state, which suffices to refute a
claimed successful continuation without assuming the attached run fails. -/
theorem workFrameCases (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (frontWork suffix joined results state joinedState : OTerm α) (psi : Formula α)
    (hn : Nonempty (Derivation body Gamma (eqn frontWork z).not))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state frontWork results)))
    (hjs : Nonempty (Derivation body Gamma (graph2 liveState joinedState joined results)))
    (kfail : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) z (state.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j)))
    (klive : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (nextWork joinedNextWork nextResults nextState joinedNextState : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph2 InternalApplicationValidityStackAppend.append joinedNextWork nextWork (suffix.relabel j))) →
      Nonempty (Derivation body Delta (graph2 liveState nextState nextWork nextResults)) →
      Nonempty (Derivation body Delta (graph2 liveState joinedNextState joinedNextWork nextResults)) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) nextState (state.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) joinedNextState (joinedState.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply nonemptyFrameCases true false guard leaf combine parameter frontWork results suffix z joined results state joinedState
    psi hn ha (identityExtend results z) hs hjs kfail
  intro β j Delta nextWork joinedNextWork nextResults framedNextResults nextState joinedNextState hj hw hr hnstate hjstate ht hjt
  change Nonempty (Derivation body Delta (graph2 (extend false) framedNextResults nextResults z)) at hr
  have he := identityExtendRecover framedNextResults nextResults z hr
  exact klive β j Delta nextWork joinedNextWork nextResults nextState joinedNextState hj hw hnstate
    (rightTransport liveState joinedNextState joinedNextWork framedNextResults nextResults he hjstate) ht hjt

/-- Result framing at arbitrary work, including empty work. An original
failure is kept separate: background results may prevent an underflow. -/
theorem resultFrameCases (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (work results background framedResults state framedState : OTerm α) (psi : Formula α)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append framedResults results background)))
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work results)))
    (hfs : Nonempty (Derivation body Gamma (graph2 liveState framedState work framedResults)))
    (kfail : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) z (state.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j)))
    (klive : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (nextWork nextResults framedNextResults nextState framedNextState : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph2 InternalApplicationValidityStackAppend.append framedNextResults nextResults (background.relabel j))) →
      Nonempty (Derivation body Delta (graph2 liveState nextState nextWork nextResults)) →
      Nonempty (Derivation body Delta (graph2 liveState framedNextState nextWork framedNextResults)) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) nextState (state.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (graph2 (transitionP guard leaf combine) framedNextState (framedState.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply formulaCases (eqn work z)
  · let Delta := eqn work z :: Gamma
    have inc : ∀ p ∈ Gamma, p ∈ Delta := fun p hp => List.mem_cons_of_mem _ hp
    have he : Nonempty (Derivation body Delta (eqn work z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hs0 := headTransport liveState state work z (Fin.cons results Fin.elim0) he (weakenProof hs inc)
    have hfs0 := headTransport liveState framedState work z (Fin.cons framedResults Fin.elim0) he (weakenProof hfs inc)
    have hout := emptyFixed guard leaf combine results state parameter (liveAsEmpty state results hs0)
    have hfout := emptyFixed guard leaf combine framedResults framedState parameter (liveAsEmpty framedState framedResults hfs0)
    have h := klive α id Delta z results framedResults state framedState
      (by intro p hp; simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using inc p hp)
      (by simpa only [Term.relabel_id] using weakenProof ha inc) hs0 hfs0
      (by simpa only [Term.relabel_id] using hout) (by simpa only [Term.relabel_id] using hfout)
    simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using h
  · let Delta := (eqn work z).not :: Gamma
    have inc : ∀ p ∈ Gamma, p ∈ Delta := fun p hp => List.mem_cons_of_mem _ hp
    apply nonemptyFrameCases false true guard leaf combine parameter work results z background work framedResults state framedState
      psi ⟨Derivation.hypothesis List.mem_cons_self⟩ (identityExtend work z)
      (weakenProof ha inc) (weakenProof hs inc) (weakenProof hfs inc)
    · intro β j Theta hj hf
      exact kfail β j Theta (fun p hp => hj p (inc p hp)) hf
    · intro β j Theta nextWork framedNextWork nextResults framedNextResults nextState framedNextState hj hw hr hnstate hfstate ht hft
      change Nonempty (Derivation body Theta (graph2 (extend false) framedNextWork nextWork z)) at hw
      have he := identityExtendRecover framedNextWork nextWork z hw
      exact klive β j Theta nextWork nextResults framedNextResults nextState framedNextState
        (fun p hp => hj p (inc p hp)) hr hnstate
        (headTransport liveState framedNextState framedNextWork nextWork (Fin.cons framedNextResults Fin.elim0) he hfstate) ht hft

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameProof
