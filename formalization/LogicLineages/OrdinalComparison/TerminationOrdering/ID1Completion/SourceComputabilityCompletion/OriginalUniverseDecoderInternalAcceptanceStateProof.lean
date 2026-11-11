module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb z eqn eqnRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof OriginalUniverseDecoderInternalAcceptanceRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem acceptedStateIntro (H : Program 1) (M W : Program 2) (state work c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H M W work c))) :
    Nonempty (Derivation body Gamma (AcceptedState H M W state c)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma (stateMatrix H M W state c)
    (fun i => emb ((![work] : Fin 1 → OTerm alpha) i))
  rw [stateMatrixWitness]
  exact andIntro hs ha

theorem acceptedStateCases (H : Program 1) (M W : Program 2) (state c : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W state c)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (work : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (StepLive (state.relabel j) work)) →
      Nonempty (Derivation body Delta (WorkAccepted H M W work (c.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma (stateMatrix H M W state c) psi ha
  apply step (alpha ⊕ Fin 1) Sum.inl
    (stateMatrix H M W state c :: Gamma.map (fun p => p.relabel Sum.inl)) (.var (.inr 0))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem acceptedStateAt (H : Program 1) (M W : Program 2) (state work c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W state c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W work c)) := by
  apply acceptedStateCases H M W state c _ ha
  intro beta j Delta actual hj hactual haccepted
  rw [workAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have he := valueUnique InternalUnpair.right actual (work.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0)
    (pairRight (state.relabel j) (numeral 1) actual hactual)
    (pairRight (state.relabel j) (numeral 1) (work.relabel j) hs')
  exact acceptedWorkTransport H M W actual (work.relabel j) (c.relabel j) he haccepted

theorem liveZeroImpossible (work : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive z work))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  have hp : Nonempty (Derivation body Gamma (StepPair (z : OTerm alpha) z z)) :=
    InternalApplicationValidityStackAppendTransitionProof.pairZero
  obtain ⟨he⟩ := valueUnique InternalUnpair.left (numeral 1) z (Fin.cons z Fin.elim0)
    (pairLeft z (numeral 1) work hs) (pairLeft z z z hp)
  exact ⟨sucNeZeroApply he⟩

theorem acceptedFailureImpossible (H : Program 1) (M W : Program 2) (c : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W (z : OTerm alpha) c))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply acceptedStateCases H M W z c _ ha
  intro beta j Delta work hj hs hw
  exact liveZeroImpossible work (by simpa only [InternalTagArithmeticSyntaxProof.zRelabel] using hs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceStateProof
