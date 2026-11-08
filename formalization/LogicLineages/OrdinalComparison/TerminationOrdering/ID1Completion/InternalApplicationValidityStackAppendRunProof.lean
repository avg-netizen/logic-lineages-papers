module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationValidityStackAppendTransitionProof
open InternalNumericIteration InternalNumericIterationProof InternalNumericIterationSupportProof
open InternalNumericIterationFixedPointProof InternalNumericIterationFusionProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionClosureLogicProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionFunctionalityProof
open InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rightTransport (p : Program 2) (out first old new : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn old new)))
    (hp : Nonempty (Derivation body Gamma (graph2 p out first old))) :
    Nonempty (Derivation body Gamma (graph2 p out first new)) := by
  apply graphInputTransport body α 2 Gamma (OrdinaryArithmetic.graphFormula p) out
    (Fin.cons first (Fin.cons old Fin.elim0)) (Fin.cons first (Fin.cons new Fin.elim0)) _ hp
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · rw [onEquality]
    exact ⟨refl first⟩
  · rw [onEquality]
    exact he

theorem successfulWorkIntro (node leaf : Program 1) (count work state : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing state (suc z) work)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationValidityStack.iterate node leaf) successState count state))) :
    Nonempty (Derivation body Gamma (successfulWork node leaf count work)) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨hr⟩ := hr
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb state)
  rw [successfulWorkInstance]
  exact Derivation.conjunctionIntroduction hs hr

theorem successfulWorkCases (node leaf : Program 1) (count work : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (successfulWork node leaf count work)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (state : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing state (suc z) (work.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 (InternalApplicationValidityStack.iterate node leaf) successState (count.relabel j) state)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := graph2 InternalPairing.pairing (.var (.inr (0 : Fin 1)))
      (suc z) (work.relabel Sum.inl) ⊓
    graph2 (InternalApplicationValidityStack.iterate node leaf) successState
      (count.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem successfulWorkAt (node leaf : Program 1) (count work state : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing state (suc z) work)))
    (h : Nonempty (Derivation body Gamma (successfulWork node leaf count work))) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationValidityStack.iterate node leaf) successState count state)) := by
  apply successfulWorkCases node leaf count work _ h
  intro β j Delta actual hj ha hr
  simp only [graph2Rename,successStateRename]
  have hs' := renameInto hs j Delta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hs'
  have he := valueUnique InternalPairing.pairing actual (state.relabel j)
    (Fin.cons (suc z) (Fin.cons (work.relabel j) Fin.elim0)) ha hs'
  exact rightTransport (InternalApplicationValidityStack.iterate node leaf)
    successState (count.relabel j) actual (state.relabel j) he hr

theorem countTransport (node leaf : Program 1) (count other work : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn count other)))
    (h : Nonempty (Derivation body Gamma (successfulWork node leaf count work))) :
    Nonempty (Derivation body Gamma (successfulWork node leaf other work)) := by
  apply successfulWorkCases node leaf count work _ h
  intro β j Delta state hj hs hr
  rw [successfulWorkRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact successfulWorkIntro node leaf (other.relabel j) (work.relabel j) state hs
    (headTransport (InternalApplicationValidityStack.iterate node leaf) successState
      (count.relabel j) (other.relabel j) (Fin.cons state Fin.elim0) he' hr)

theorem workTransport (node leaf : Program 1) (count work other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn work other)))
    (h : Nonempty (Derivation body Gamma (successfulWork node leaf count work))) :
    Nonempty (Derivation body Gamma (successfulWork node leaf count other)) := by
  apply successfulWorkCases node leaf count work _ h
  intro β j Delta state hj hs hr
  rw [successfulWorkRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact successfulWorkIntro node leaf (count.relabel j) (other.relabel j) state
    (rightTransport InternalPairing.pairing state (suc z) (work.relabel j) (other.relabel j) he' hs) hr

theorem zeroWork (node leaf : Program 1) (work : OTerm α)
    (h : Nonempty (Derivation body Gamma (successfulWork node leaf z work))) :
    Nonempty (Derivation body Gamma (eqn work z)) := by
  apply successfulWorkCases node leaf z work _ h
  intro β j Delta state _ hs hr
  simp only [eqnRelabel,zRelabel]
  simp only [zRelabel] at hr
  obtain ⟨he⟩ := repeatZeroRecover (InternalApplicationValidityStack.transition node leaf)
    successState state hr
  have hw := headTransport InternalUnpair.right (work.relabel j) state successState Fin.elim0
    ⟨symm he⟩ (pairRight state (suc z) (work.relabel j) hs)
  exact valueUnique InternalUnpair.right (work.relabel j) z (Fin.cons successState Fin.elim0)
    hw (pairRight successState (suc z) z pairOneZero)

theorem nilSuccess (node leaf : Program 1) (count : OTerm α) :
    Nonempty (Derivation body Gamma (successfulWork node leaf count z)) :=
  successfulWorkIntro node leaf count z successState pairOneZero
    (fixedValue (InternalApplicationValidityStack.transition node leaf) count successState
      (terminalFixed node leaf))

theorem successPadding (node leaf : Program 1) (count padding work : OTerm α)
    (h : Nonempty (Derivation body Gamma (successfulWork node leaf count work))) :
    Nonempty (Derivation body Gamma
      (successfulWork node leaf (OrdinaryArithmetic.addTerm count padding) work)) := by
  apply successfulWorkCases node leaf count work _ h
  intro β j Delta state _ hs hr
  simp only [successfulWorkRename,InternalOriginalOrderSyntaxProof.addRelabel]
  exact successfulWorkIntro node leaf
    (OrdinaryArithmetic.addTerm (count.relabel j) (padding.relabel j)) (work.relabel j) state hs
    (fusionValue (InternalApplicationValidityStack.transition node leaf)
      (count.relabel j) (padding.relabel j) state successState successState hr
      (fixedValue (InternalApplicationValidityStack.transition node leaf) (padding.relabel j)
        successState (terminalFixed node leaf)))

theorem failureImpossible (node leaf : Program 1) (count : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (graph2 (InternalApplicationValidityStack.iterate node leaf) successState count z))) :
    Nonempty (Derivation body Gamma (⊥ : Formula α)) := by
  obtain ⟨he⟩ := valueUnique (InternalApplicationValidityStack.iterate node leaf) successState z
    (Fin.cons count (Fin.cons z Fin.elim0)) h
    (fixedValue (InternalApplicationValidityStack.transition node leaf) count z (failureFixed node leaf))
  exact ⟨sucNeZeroApply he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
