module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalApplicationResultStackCompositionSyntaxProof InternalApplicationResultStackCompositionStateProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityStackAppendRunProof (rightTransport)
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

theorem runEndIntro (guard leaf : Program 1) (combine : Program 4)
    (count state finalResults finalState : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState finalState finalResults)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationResultStack.iterate guard leaf combine) finalState count state))) :
    Nonempty (Derivation body Gamma (runEnd guard leaf combine count state finalResults)) := by
  obtain ⟨h⟩ := andIntro he hr
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb finalState)
  rw [runEndInstance]
  exact h

theorem runEndCases (guard leaf : Program 1) (combine : Program 4)
    (count state finalResults : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (runEnd guard leaf combine count state finalResults)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (finalState : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph1 InternalApplicationResultStack.emptyState finalState (finalResults.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 (InternalApplicationResultStack.iterate guard leaf combine)
          finalState (count.relabel j) (state.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := graph1 InternalApplicationResultStack.emptyState (.var (.inr (0 : Fin 1)))
      (finalResults.relabel Sum.inl) ⊓
    graph2 (InternalApplicationResultStack.iterate guard leaf combine)
      (.var (.inr (0 : Fin 1))) (count.relabel Sum.inl) (state.relabel Sum.inl)
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem runInitialIntro (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults state : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work initialResults)))
    (hr : Nonempty (Derivation body Gamma (runEnd guard leaf combine count state finalResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults)) := by
  obtain ⟨h⟩ := andIntro hs hr
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb state)
  change Derivation body Gamma (instantiate
    (graph2 liveState (.var (.inr (0 : Fin 1))) (work.relabel Sum.inl) (initialResults.relabel Sum.inl) ⊓
      runEnd guard leaf combine (count.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
        (finalResults.relabel Sum.inl)) (emb state))
  rw [actualRunInstance]
  exact h

theorem runInitialCases (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (state : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 liveState state (work.relabel j) (initialResults.relabel j))) →
      Nonempty (Derivation body Delta
        (runEnd guard leaf combine (count.relabel j) state (finalResults.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := graph2 liveState (.var (.inr (0 : Fin 1)))
      (work.relabel Sum.inl) (initialResults.relabel Sum.inl) ⊓
    runEnd guard leaf combine (count.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
      (finalResults.relabel Sum.inl)
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem runIntro (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults state finalState : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work initialResults)))
    (he : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState finalState finalResults)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationResultStack.iterate guard leaf combine) finalState count state))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults)) :=
  runInitialIntro guard leaf combine count work initialResults finalResults state hs
    (runEndIntro guard leaf combine count state finalResults finalState he hr)

theorem runCases (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (state finalState : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 liveState state (work.relabel j) (initialResults.relabel j))) →
      Nonempty (Derivation body Delta
        (graph1 InternalApplicationResultStack.emptyState finalState (finalResults.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 (InternalApplicationResultStack.iterate guard leaf combine) finalState (count.relabel j) state)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply runInitialCases guard leaf combine count work initialResults finalResults psi h
  intro β j Delta state hj hs hr
  apply runEndCases guard leaf combine (count.relabel j) state (finalResults.relabel j) _ hr
  intro γ l Theta finalState hl he ht
  have hs' := renameInto hs l Theta hl
  simp only [graph2Rename,Term.relabel_relabel] at hs'
  simp only [Term.relabel_relabel] at he ht
  have hk := k γ (l ∘ j) Theta (state.relabel l) finalState
    (fun p hp => by simpa only [formulaRelabelComposition] using hl (p.relabel j) (hj p hp)) hs' he ht
  simpa only [formulaRelabelComposition] using hk

theorem runAt (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults state finalState : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state work initialResults)))
    (he : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState finalState finalResults)))
    (hr : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationResultStack.iterate guard leaf combine) finalState count state)) := by
  apply runCases guard leaf combine count work initialResults finalResults _ hr
  intro β j Delta actual actualFinal hj ha haf ht
  simp only [graph2Rename]
  have hs' := renameInto hs j Delta hj
  have he' := renameInto he j Delta hj
  simp only [graph2Rename] at hs'
  simp only [graph1Rename] at he'
  have hsi := valueUnique liveState actual (state.relabel j)
    (Fin.cons (work.relabel j) (Fin.cons (initialResults.relabel j) Fin.elim0)) ha hs'
  have hsf := valueUnique InternalApplicationResultStack.emptyState actualFinal (finalState.relabel j)
    (Fin.cons (finalResults.relabel j) Fin.elim0) haf he'
  exact outputTransport (InternalApplicationResultStack.iterate guard leaf combine) actualFinal
    (finalState.relabel j) (Fin.cons (count.relabel j) (Fin.cons (state.relabel j) Fin.elim0)) hsf
    (rightTransport (InternalApplicationResultStack.iterate guard leaf combine)
      actualFinal (count.relabel j) actual (state.relabel j) hsi ht)

theorem countTransport (guard leaf : Program 1) (combine : Program 4)
    (count other work initialResults finalResults : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn count other)))
    (hr : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine other work initialResults finalResults)) := by
  apply runCases guard leaf combine count work initialResults finalResults _ hr
  intro β j Delta state finalState hj hs hf ht
  rw [actualRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact runIntro guard leaf combine (other.relabel j) (work.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) state finalState hs hf
    (headTransport (InternalApplicationResultStack.iterate guard leaf combine) finalState
      (count.relabel j) (other.relabel j) (Fin.cons state Fin.elim0) he' ht)

theorem workTransport (guard leaf : Program 1) (combine : Program 4)
    (count work other initialResults finalResults : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn work other)))
    (hr : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine count other initialResults finalResults)) := by
  apply runCases guard leaf combine count work initialResults finalResults _ hr
  intro β j Delta state finalState hj hs hf ht
  rw [actualRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact runIntro guard leaf combine (count.relabel j) (other.relabel j)
    (initialResults.relabel j) (finalResults.relabel j) state finalState
    (headTransport liveState state (work.relabel j) (other.relabel j)
      (Fin.cons (initialResults.relabel j) Fin.elim0) he' hs) hf ht

theorem initialResultsTransport (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults other finalResults : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn initialResults other)))
    (hr : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine count work other finalResults)) := by
  apply runCases guard leaf combine count work initialResults finalResults _ hr
  intro β j Delta state finalState hj hs hf ht
  rw [actualRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact runIntro guard leaf combine (count.relabel j) (work.relabel j)
    (other.relabel j) (finalResults.relabel j) state finalState
    (rightTransport liveState state (work.relabel j) (initialResults.relabel j) (other.relabel j) he' hs) hf ht

theorem finalResultsTransport (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn finalResults other)))
    (hr : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults other)) := by
  apply runCases guard leaf combine count work initialResults finalResults _ hr
  intro β j Delta state finalState hj hs hf ht
  rw [actualRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact runIntro guard leaf combine (count.relabel j) (work.relabel j)
    (initialResults.relabel j) (other.relabel j) state finalState hs
    (headTransport InternalApplicationResultStack.emptyState finalState
      (finalResults.relabel j) (other.relabel j) Fin.elim0 he' hf) ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionRunProof
