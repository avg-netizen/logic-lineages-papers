module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingMapProof
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
open InternalBetaTotalityProof

theorem localCases (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (CoupledLocal H kind mode gamma typ tag payload rest joinedRest suffix)))
    (kfail : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (LocalSpec H kind z (mode.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) (rest.relabel j))) →
      Nonempty (Derivation body Theta
        (LocalSpec H kind z (mode.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) (joinedRest.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (klive : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontNext joinedNext nextState joinedNextState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StepLive nextState frontNext)) →
      Nonempty (Derivation body Theta (StepLive joinedNextState joinedNext)) →
      Nonempty (Derivation body Theta
        (LocalSpec H kind nextState (mode.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) (rest.relabel j))) →
      Nonempty (Derivation body Theta
        (LocalSpec H kind joinedNextState (mode.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) (joinedRest.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let A := LocalSpec H kind z mode gamma typ tag payload rest ⊓
    LocalSpec H kind z mode gamma typ tag payload joinedRest
  let B := InternalFiniteBlocks.block (localLiveMatrix H kind mode gamma typ tag payload rest joinedRest suffix)
  have hleft : Nonempty (Derivation body (A :: Delta) psi) := by
    have h := kfail alpha id (A :: Delta)
      (fun p hp => by simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using
        List.mem_cons_of_mem A hp)
      (by simpa only [Term.relabel_id] using
        (show Nonempty (Derivation body (A :: Delta) (LocalSpec H kind z mode gamma typ tag payload rest)) from
          ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩))
      (by simpa only [Term.relabel_id] using
        (show Nonempty (Derivation body (A :: Delta) (LocalSpec H kind z mode gamma typ tag payload joinedRest)) from
          ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩))
    simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using h
  have hright : Nonempty (Derivation body (B :: Delta) psi) := by
    apply InternalFiniteBlocksProof.elimination body alpha 4 (B :: Delta)
      (localLiveMatrix H kind mode gamma typ tag payload rest joinedRest suffix) psi
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply klive (alpha ⊕ Fin 4) Sum.inl
      (localLiveMatrix H kind mode gamma typ tag payload rest joinedRest suffix ::
        (B :: Delta).map (fun p => p.relabel Sum.inl))
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

/-- Lift a local arithmetic clause into its original surrounding dispatch. -/
theorem mapCoupling (H : Program 1) (source target : Kind)
    (mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (CoupledLocal H source mode gamma typ tag payload rest joinedRest suffix)))
    (hm : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (out tail : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (LocalSpec H source out (mode.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) tail)) →
      Nonempty (Derivation body Theta
        (LocalSpec H target out (mode.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) tail))) :
    Nonempty (Derivation body Delta (CoupledLocal H target mode gamma typ tag payload rest joinedRest suffix)) := by
  apply localCases H source mode gamma typ tag payload rest joinedRest suffix _ hc
  · intro beta j Theta hj hs hjs
    rw [localCoupledRename]
    exact localFailureIntro H target _ _ _ _ _ _ _ _
      (hm beta j Theta z (rest.relabel j) hj hs)
      (hm beta j Theta z (joinedRest.relabel j) hj hjs)
  · intro beta j Theta fw jw fs js hj ha hf hjf hs hjs
    rw [localCoupledRename]
    exact localLiveIntro H target _ _ _ _ _ _ _ _ fw jw fs js ha hf hjf
      (hm beta j Theta fs (rest.relabel j) hj hs)
      (hm beta j Theta js (joinedRest.relabel j) hj hjs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingMapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingMapProof
