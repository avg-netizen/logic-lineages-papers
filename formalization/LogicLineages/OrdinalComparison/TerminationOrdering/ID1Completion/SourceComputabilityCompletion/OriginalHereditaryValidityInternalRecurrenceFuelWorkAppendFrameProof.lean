module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSyntaxProof
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Eliminate the two actual transition outputs and their shared suffix.
Every witness is supplied by the independent internal one-step coupling. -/
theorem coupledCases (s t m : Program 2) (state joinedState suffix : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)))
    (kfail : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (transition s t m) z (state.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (transition s t m) z (joinedState.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (klive : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontNext joinedNext nextState joinedNextState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StateGraph nextState (numeral 1) frontNext)) →
      Nonempty (Derivation body Theta (StateGraph joinedNextState (numeral 1) joinedNext)) →
      Nonempty (Derivation body Theta (graph1 (transition s t m) nextState (state.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (transition s t m) joinedNextState (joinedState.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let A := graph1 (transition s t m) z state ⊓ graph1 (transition s t m) z joinedState
  let B := InternalFiniteBlocks.block (liveMatrix s t m state joinedState suffix)
  have hleft : Nonempty (Derivation body (A :: Delta) psi) := by
    have h := kfail alpha id (A :: Delta)
      (fun p hp => by simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using
        List.mem_cons_of_mem A hp)
      (by simpa only [Term.relabel_id] using
        (show Nonempty (Derivation body (A :: Delta) (graph1 (transition s t m) z state)) from
          ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩))
      (by simpa only [Term.relabel_id] using
        (show Nonempty (Derivation body (A :: Delta) (graph1 (transition s t m) z joinedState)) from
          ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩))
    simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using h
  have hright : Nonempty (Derivation body (B :: Delta) psi) := by
    apply InternalFiniteBlocksProof.elimination body alpha 4 (B :: Delta)
      (liveMatrix s t m state joinedState suffix) psi ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply klive (alpha ⊕ Fin 4) Sum.inl
      (liveMatrix s t m state joinedState suffix :: (B :: Delta).map (fun p => p.relabel Sum.inl))
      (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
    · intro p hp
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,List.mem_cons_of_mem B hp,rfl⟩)
    · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    · exact ⟨Derivation.conjunctionLeft
        (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    · exact ⟨Derivation.conjunctionLeft
        (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)))⟩
    · exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight
        (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))))⟩
    · exact ⟨Derivation.conjunctionRight (Derivation.conjunctionRight
        (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))))⟩
  obtain ⟨hc⟩ := hc
  obtain ⟨hl⟩ := hleft
  obtain ⟨hr⟩ := hright
  exact ⟨disjunctionElimination hc
    (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem frameCases (s t m : Program 2) (front suffix joined state joinedState : OTerm alpha) (psi : Formula alpha)
    (hnz : Nonempty (Derivation body Delta (eqn front z).not))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hs : Nonempty (Derivation body Delta (StateGraph state (numeral 1) front)))
    (hjs : Nonempty (Derivation body Delta (StateGraph joinedState (numeral 1) joined)))
    (kfail : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (transition s t m) z (state.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (transition s t m) z (joinedState.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (klive : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontNext joinedNext nextState joinedNextState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StateGraph nextState (numeral 1) frontNext)) →
      Nonempty (Derivation body Theta (StateGraph joinedNextState (numeral 1) joinedNext)) →
      Nonempty (Derivation body Theta (graph1 (transition s t m) nextState (state.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (transition s t m) joinedNextState (joinedState.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) :=
  coupledCases s t m state joinedState suffix psi
    (frameCoupling s t m front suffix joined state joinedState hnz ha hs hjs) kfail klive

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendFrameProof
