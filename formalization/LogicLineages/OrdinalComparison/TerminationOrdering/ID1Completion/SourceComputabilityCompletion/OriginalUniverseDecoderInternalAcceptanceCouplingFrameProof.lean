module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
open OriginalTypedDecoderInternalAcceptanceCouplingMapProof
open OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
open OriginalTypedDecoderInternalAcceptanceCouplingDispatchProof
open OriginalUniverseDecoderInternalAcceptanceCouplingStateSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceCouplingStateProof
open InternalBetaTotalityProof

/-- Eliminate the two actual guarded-source outputs and their shared suffix.
Both branches retain the SAME separate outer context, including rejection. -/
theorem coupledCases (H : Program 1) (M W : Program 2) (state joinedState suffix c : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (CoupledStep H M W state joinedState suffix c)))
    (kfail : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.transition H M W) z (state.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.transition H M W) z (joinedState.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (klive : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontNext joinedNext nextState joinedNextState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StepLive nextState frontNext)) →
      Nonempty (Derivation body Theta (StepLive joinedNextState joinedNext)) →
      Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.transition H M W) nextState (state.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.transition H M W) joinedNextState (joinedState.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let A := graph2 (OriginalUniverseDecoder.transition H M W) z state c ⊓ graph2 (OriginalUniverseDecoder.transition H M W) z joinedState c
  let B := InternalFiniteBlocks.block (liveMatrix H M W state joinedState suffix c)
  have hleft : Nonempty (Derivation body (A :: Delta) psi) := by
    have h := kfail alpha id (A :: Delta)
      (fun p hp => by simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using
        List.mem_cons_of_mem A hp)
      (by simpa only [Term.relabel_id] using
        (show Nonempty (Derivation body (A :: Delta) (graph2 (OriginalUniverseDecoder.transition H M W) z state c)) from
          ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩))
      (by simpa only [Term.relabel_id] using
        (show Nonempty (Derivation body (A :: Delta) (graph2 (OriginalUniverseDecoder.transition H M W) z joinedState c)) from
          ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩))
    simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using h
  have hright : Nonempty (Derivation body (B :: Delta) psi) := by
    apply InternalFiniteBlocksProof.elimination body alpha 4 (B :: Delta)
      (liveMatrix H M W state joinedState suffix c) psi ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply klive (alpha ⊕ Fin 4) Sum.inl
      (liveMatrix H M W state joinedState suffix c :: (B :: Delta).map (fun p => p.relabel Sum.inl))
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

theorem frameCases (H : Program 1) (M W : Program 2) (front suffix joined state joinedState c : OTerm alpha) (psi : Formula alpha)
    (hnz : Nonempty (Derivation body Delta (eqn front z).not))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hs : Nonempty (Derivation body Delta (StepLive state front)))
    (hjs : Nonempty (Derivation body Delta (StepLive joinedState joined)))
    (kfail : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.transition H M W) z (state.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.transition H M W) z (joinedState.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (klive : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontNext joinedNext nextState joinedNextState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StepLive nextState frontNext)) →
      Nonempty (Derivation body Theta (StepLive joinedNextState joinedNext)) →
      Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.transition H M W) nextState (state.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (OriginalUniverseDecoder.transition H M W) joinedNextState (joinedState.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) :=
  coupledCases H M W state joinedState suffix c psi
    (frameCoupling H M W front suffix joined state joinedState c hnz ha hs hjs) kfail klive

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingFrameProof
