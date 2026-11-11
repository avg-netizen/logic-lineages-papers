module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind)
open SourceComputabilityFormulaSupportProof (existsOne)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stepBinaryPayloadSubst {beta : Type}
    (payload domain first second : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepBinaryPayload payload domain first second).subst (fun a => emb (ts a)) =
      StepBinaryPayload (payload.subst ts) (domain.subst ts) (first.subst ts) (second.subst ts) := by
  unfold StepBinaryPayload
  rw [existsSubst,liftedEmbedding]
  simp only [conjunctionSubst,stepPairSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem stepBinaryPayloadRename {beta : Type}
    (payload domain first second : OTerm alpha) (j : alpha → beta) :
    (StepBinaryPayload payload domain first second).relabel j =
      StepBinaryPayload (payload.relabel j) (domain.relabel j) (first.relabel j) (second.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepBinaryPayload payload domain first second).subst (fun a => emb (.var (j a))) = _
  rw [stepBinaryPayloadSubst]
  simp only [← termRelabelAsSubst]

theorem stepBinaryPayloadInstantiate (payload domain first second tail : OTerm alpha) :
    instantiate
      (StepPair (payload.relabel Sum.inl) (domain.relabel Sum.inl) (.var (.inr 0)) ⊓
        StepPair (.var (.inr 0)) (first.relabel Sum.inl) (second.relabel Sum.inl))
      (emb tail) = StepPair payload domain tail ⊓ StepPair tail first second := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [stepPairSubst,varBind,liftBind]

theorem stepBinaryPayloadIntro (payload domain first second tail : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (StepPair payload domain tail)))
    (hf : Nonempty (Derivation body Delta (StepPair tail first second))) :
    Nonempty (Derivation body Delta (StepBinaryPayload payload domain first second)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hf⟩ := hf
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb tail)
  rw [stepBinaryPayloadInstantiate]
  exact Derivation.conjunctionIntroduction hp hf

theorem stepBinaryPayloadCases (payload domain first second : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepBinaryPayload payload domain first second)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (tail : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (StepPair (payload.relabel j) (domain.relabel j) tail)) →
      Nonempty (Derivation body Theta
        (StepPair tail (first.relabel j) (second.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  let P := StepPair (payload.relabel Sum.inl) (domain.relabel Sum.inl) (.var (.inr (0 : Fin 1))) ⊓
    StepPair (.var (.inr 0)) (first.relabel Sum.inl) (second.relabel Sum.inl)
  let Theta := P :: Delta.map weaken
  obtain ⟨d⟩ := k (alpha ⊕ Fin 1) Sum.inl Theta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
