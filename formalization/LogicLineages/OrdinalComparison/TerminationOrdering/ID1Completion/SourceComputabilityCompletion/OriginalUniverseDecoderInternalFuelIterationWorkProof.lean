module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationWorkProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationWorkProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalSourceInversionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb eqn eqnRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (WorkFuelGraph Terminal)
open OriginalTypedDecoderInternalFuelIterationWorkProof (binaryRightTransport)
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem ternaryMiddleTransport (p : Program 3) (out first old new c : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn old new)))
    (hp : Nonempty (Derivation body Gamma (graph3 p out first old c))) :
    Nonempty (Derivation body Gamma (graph3 p out first new c)) := by
  apply graphInputTransport body alpha 3 Gamma (OrdinaryArithmetic.graphFormula p) out
    ![first,old,c] ![first,new,c] _ hp
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
  · rw [onEquality]; exact ⟨refl first⟩
  · rw [onEquality]; exact he
  · rw [onEquality]; exact ⟨refl c⟩

theorem workRunIntro (H : Program 1) (M contextWindow : Program 2) (out count workCode state c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hr : Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) out count state c))) :
    Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count workCode c)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma
    (runMatrix H M contextWindow out count workCode c) (fun i => emb ((![state] : Fin 1 → OTerm alpha) i))
  rw [runMatrixWitness]
  exact andIntro hs hr

theorem workRunCases (H : Program 1) (M contextWindow : Program 2) (out count workCode c : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count workCode c)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (state : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (StepLive state (workCode.relabel j))) →
      Nonempty (Derivation body Delta
        (graph3 (iterate H M contextWindow) (out.relabel j) (count.relabel j) state (c.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma
    (runMatrix H M contextWindow out count workCode c) psi h
  apply step (alpha ⊕ Fin 1) Sum.inl
    (runMatrix H M contextWindow out count workCode c :: Gamma.map (fun p => p.relabel Sum.inl)) (.var (.inr 0))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem workRunAt (H : Program 1) (M contextWindow : Program 2) (out count workCode state c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hr : Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count workCode c))) :
    Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) out count state c)) := by
  apply workRunCases H M contextWindow out count workCode c _ hr
  intro beta j Delta actual hj ha hi
  rw [graph3Rename]
  have hs' := renameInto hs j Delta hj
  simp only [OriginalTypedDecoderInternalScalarSyntaxProof.stepLiveRename] at hs'
  have he := valueUnique InternalPairing.pairing actual (state.relabel j)
    (Fin.cons (numeral 1) (Fin.cons (workCode.relabel j) Fin.elim0)) ha hs'
  exact ternaryMiddleTransport (iterate H M contextWindow) (out.relabel j) (count.relabel j)
    actual (state.relabel j) (c.relabel j) he hi

theorem terminatedIntro (H : Program 1) (M contextWindow : Program 2) (count workCode out c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count workCode c)))
    (ht : Nonempty (Derivation body Gamma (Terminal out))) :
    Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow count workCode c)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma
    (terminatedMatrix H M contextWindow count workCode c) (fun i => emb ((![out] : Fin 1 → OTerm alpha) i))
  rw [terminatedMatrixWitness]
  exact andIntro hr ht

theorem terminatedCases (H : Program 1) (M contextWindow : Program 2) (count workCode c : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow count workCode c)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (WorkRun H M contextWindow out (count.relabel j) (workCode.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Delta (Terminal out)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma
    (terminatedMatrix H M contextWindow count workCode c) psi h
  apply step (alpha ⊕ Fin 1) Sum.inl
    (terminatedMatrix H M contextWindow count workCode c :: Gamma.map (fun p => p.relabel Sum.inl)) (.var (.inr 0))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem acceptedIntro (H : Program 1) (M contextWindow : Program 2) (workCode count c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph count workCode)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow count workCode c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M contextWindow workCode c)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma
    (acceptedMatrix H M contextWindow workCode c) (fun i => emb ((![count] : Fin 1 → OTerm alpha) i))
  rw [acceptedMatrixWitness]
  exact andIntro hf hs

theorem acceptedCases (H : Program 1) (M contextWindow : Program 2) (workCode c : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (WorkAccepted H M contextWindow workCode c)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (count : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (WorkFuelGraph count (workCode.relabel j))) →
      Nonempty (Derivation body Delta (SuccessfulWork H M contextWindow count (workCode.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma
    (acceptedMatrix H M contextWindow workCode c) psi h
  apply step (alpha ⊕ Fin 1) Sum.inl
    (acceptedMatrix H M contextWindow workCode c :: Gamma.map (fun p => p.relabel Sum.inl)) (.var (.inr 0))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem workRunCountTransport (H : Program 1) (M contextWindow : Program 2) (out count other workCode c : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn count other)))
    (hr : Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count workCode c))) :
    Nonempty (Derivation body Gamma (WorkRun H M contextWindow out other workCode c)) := by
  apply workRunCases H M contextWindow out count workCode c _ hr
  intro beta j Delta state hj hs hi
  rw [workRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact workRunIntro H M contextWindow (out.relabel j) (other.relabel j) (workCode.relabel j) state (c.relabel j) hs
    (headTransport (iterate H M contextWindow) (out.relabel j) (count.relabel j) (other.relabel j)
      ![state,c.relabel j] he' hi)

theorem workRunWorkTransport (H : Program 1) (M contextWindow : Program 2) (out count workCode other c : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (eqn workCode other)))
    (hr : Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count workCode c))) :
    Nonempty (Derivation body Gamma (WorkRun H M contextWindow out count other c)) := by
  apply workRunCases H M contextWindow out count workCode c _ hr
  intro beta j Delta state hj hs hi
  rw [workRunRename]
  have he' := renameInto he j Delta hj
  rw [eqnRelabel] at he'
  exact workRunIntro H M contextWindow (out.relabel j) (count.relabel j) (other.relabel j) state (c.relabel j)
    (binaryRightTransport InternalPairing.pairing state (numeral 1)
      (workCode.relabel j) (other.relabel j) he' hs) hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationWorkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationWorkProof
