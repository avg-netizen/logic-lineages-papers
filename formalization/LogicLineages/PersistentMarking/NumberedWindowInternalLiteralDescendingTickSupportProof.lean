module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFirstTickAllCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRunTerminalFlagProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingTickSupportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport programRename zeroSuccessorCases)
open ID1Completion.InternalTagArithmeticSupportProof (congTerm symm trans)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (eqn bindTerm liftBind varBind eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalOriginalOrderProof (orderCases actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateSubst stateRename)
open NumberedWindowInternalLiteralFirstTickAllCasesProof (TickAt)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (D)
open NumberedWindowInternalLiteralRunTerminalFlagProof (starterRename)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveOrderRight (x a b : OTerm α) (h : D B Γ (ltF x a)) (e : D B Γ (eqn a b)) :
    D B Γ (ltF x b) := by
  apply orderCases Γ x a (ltF x b) h
  intro β j Δ gap keep given
  rw [orderRename]
  have eq := renameInto e j Δ keep
  rw [eqnRelabel] at eq
  obtain ⟨s⟩ := given
  obtain ⟨t⟩ := eq
  apply actualOriginalOrderIntroduction B β Δ _ _ gap
  rw [onEquality]
  exact ⟨ID1Completion.InternalTagArithmeticSupportProof.trans s t⟩

theorem frameEq (flag a b : OTerm α) (h : D B Γ (eqn a b)) :
    D B Γ (eqn (stateTerm flag a) (stateTerm flag b)) := by
  obtain ⟨e⟩ := h
  have r := congTerm (stateTerm (flag.relabel Sum.inl) (.var (.inr 0))) e
  exact ⟨by simpa only [stateSubst,liftBind,varBind] using r⟩

theorem tickFrame (p other : Program 3) (flag a b q w r : OTerm α)
    (h : D B Γ (TickAt p other flag a q w r)) (e : D B Γ (eqn a b)) :
    D B Γ (TickAt p other flag b q w r) := by
  apply outputTransport (chosenTick p other) (stateTerm flag a) (stateTerm flag b)
    ![initialTerm (![q,w,r])] (frameEq flag a b e) h

theorem tickRename {β : Type} (p other : Program 3) (flag frame q w r : OTerm α) (j : α → β) :
    (TickAt p other flag frame q w r).relabel j =
      TickAt p other (flag.relabel j) (frame.relabel j) (q.relabel j) (w.relabel j) (r.relabel j) := by
  unfold TickAt
  rw [programRename,inputsRename,stateRename,starterRename]

/-- Normalize the frame of the actual first tick internally. Rejection
uses the same tick with frame zero. In the positive case the equality
retains the actual computed predecessor of the scratch frame. -/
theorem tickFrameCases (p other : Program 3) (q w r frame : OTerm α) (goal : Formula α)
    (held : D B Γ (TickAt p other z frame q w r))
    (rejected : ∀ Δ : List (Formula α), (∀ f ∈ Γ, f ∈ Δ) →
      D B Δ (TickAt p other z z q w r) → D B Δ goal)
    (positive : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (n : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (frame.relabel j) (suc n)) →
      D B Δ (TickAt p other z (suc n) (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply zeroSuccessorCases Γ frame goal
  · let Δ := eqn frame z :: Γ
    obtain ⟨t⟩ := held
    exact rejected Δ (fun f h => List.mem_cons_of_mem _ h)
      (tickFrame p other z frame z q w r ⟨addHyp t _⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩)
  · intro β j Δ n keep equal
    have t := renameInto held j Δ keep
    rw [tickRename,zRelabel] at t
    exact positive β j Δ n keep equal
      (tickFrame p other z (frame.relabel j) (suc n) (q.relabel j) (w.relabel j) (r.relabel j) t equal)

#print axioms tickFrameCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingTickSupportProof
