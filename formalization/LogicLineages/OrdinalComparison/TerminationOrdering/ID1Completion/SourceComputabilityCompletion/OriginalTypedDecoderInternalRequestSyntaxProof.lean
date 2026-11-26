module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


def stepRequestFields ( request mode gamma typ raw : OTerm alpha) (ys : Fin 2 → OTerm alpha) : Formula alpha :=
  StepPair request mode (ys 0) ⊓
    (StepPair (ys 0) gamma (ys 1) ⊓ StepPair (ys 1) typ raw)

def stepRequestMatrix (request mode gamma typ raw : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  stepRequestFields (request.relabel Sum.inl) (mode.relabel Sum.inl) (gamma.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) (fun i => .var (.inr i))

theorem stepRequestFieldsSubst {beta : Type} (request mode gamma typ raw : OTerm alpha)
    (ys : Fin 2 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stepRequestFields request mode gamma typ raw ys).subst (fun a => emb (ts a)) =
      stepRequestFields (request.subst ts) (mode.subst ts) (gamma.subst ts) (typ.subst ts) (raw.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stepRequestFields,conjunctionSubst,stepPairSubst]

theorem stepRequestMatrixWitness (request mode gamma typ raw : OTerm alpha) (ys : Fin 2 → OTerm alpha) :
    (stepRequestMatrix request mode gamma typ raw).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stepRequestFields request mode gamma typ raw ys := by
  unfold stepRequestMatrix
  rw [witnessEmbedding,stepRequestFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stepRequestIntro (request mode gamma typ raw : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepRequestFields request mode gamma typ raw ys))) :
    Nonempty (Derivation body Delta (StepRequest request mode gamma typ raw)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta
    (stepRequestMatrix request mode gamma typ raw) (fun i => emb (ys i))
  rw [stepRequestMatrixWitness]
  exact h

theorem stepRequestCases (request mode gamma typ raw : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepRequest request mode gamma typ raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 2 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stepRequestFields (request.relabel j) (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (stepRequestMatrix request mode gamma typ raw) psi h
  apply step (alpha ⊕ Fin 2) Sum.inl
    (stepRequestMatrix request mode gamma typ raw :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stepRequestSubst {beta : Type} (request mode gamma typ raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepRequest request mode gamma typ raw).subst (fun a => emb (ts a)) = StepRequest (request.subst ts) (mode.subst ts) (gamma.subst ts) (typ.subst ts) (raw.subst ts) := by
  change (InternalFiniteBlocks.block (stepRequestMatrix request mode gamma typ raw)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stepRequestMatrix
  simp only [stepRequestFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepRequestRename {beta : Type} (request mode gamma typ raw : OTerm alpha) (j : alpha → beta) :
    (StepRequest request mode gamma typ raw).relabel j = StepRequest (request.relabel j) (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepRequest request mode gamma typ raw).subst (fun a => emb (.var (j a))) = _
  rw [stepRequestSubst]
  simp only [← termRelabelAsSubst]

def stepNumberedPayloadFields ( payload label head result base types extras : OTerm alpha) (ys : Fin 4 → OTerm alpha) : Formula alpha :=
  StepPair payload label (ys 0) ⊓
    (StepPair (ys 0) head (ys 1) ⊓
      (StepPair (ys 1) result (ys 2) ⊓
        (StepPair (ys 2) base (ys 3) ⊓ StepPair (ys 3) types extras)))

def stepNumberedPayloadMatrix (payload label head result base types extras : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  stepNumberedPayloadFields (payload.relabel Sum.inl) (label.relabel Sum.inl) (head.relabel Sum.inl) (result.relabel Sum.inl) (base.relabel Sum.inl) (types.relabel Sum.inl) (extras.relabel Sum.inl) (fun i => .var (.inr i))

theorem stepNumberedPayloadFieldsSubst {beta : Type} (payload label head result base types extras : OTerm alpha)
    (ys : Fin 4 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stepNumberedPayloadFields payload label head result base types extras ys).subst (fun a => emb (ts a)) =
      stepNumberedPayloadFields (payload.subst ts) (label.subst ts) (head.subst ts) (result.subst ts) (base.subst ts) (types.subst ts) (extras.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stepNumberedPayloadFields,conjunctionSubst,stepPairSubst]

theorem stepNumberedPayloadMatrixWitness (payload label head result base types extras : OTerm alpha) (ys : Fin 4 → OTerm alpha) :
    (stepNumberedPayloadMatrix payload label head result base types extras).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stepNumberedPayloadFields payload label head result base types extras ys := by
  unfold stepNumberedPayloadMatrix
  rw [witnessEmbedding,stepNumberedPayloadFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stepNumberedPayloadIntro (payload label head result base types extras : OTerm alpha) (ys : Fin 4 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepNumberedPayloadFields payload label head result base types extras ys))) :
    Nonempty (Derivation body Delta (StepNumberedPayload payload label head result base types extras)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 4 Delta
    (stepNumberedPayloadMatrix payload label head result base types extras) (fun i => emb (ys i))
  rw [stepNumberedPayloadMatrixWitness]
  exact h

theorem stepNumberedPayloadCases (payload label head result base types extras : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepNumberedPayload payload label head result base types extras)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 4 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stepNumberedPayloadFields (payload.relabel j) (label.relabel j) (head.relabel j) (result.relabel j) (base.relabel j) (types.relabel j) (extras.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 4 Delta (stepNumberedPayloadMatrix payload label head result base types extras) psi h
  apply step (alpha ⊕ Fin 4) Sum.inl
    (stepNumberedPayloadMatrix payload label head result base types extras :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stepNumberedPayloadSubst {beta : Type} (payload label head result base types extras : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepNumberedPayload payload label head result base types extras).subst (fun a => emb (ts a)) = StepNumberedPayload (payload.subst ts) (label.subst ts) (head.subst ts) (result.subst ts) (base.subst ts) (types.subst ts) (extras.subst ts) := by
  change (InternalFiniteBlocks.block (stepNumberedPayloadMatrix payload label head result base types extras)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stepNumberedPayloadMatrix
  simp only [stepNumberedPayloadFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepNumberedPayloadRename {beta : Type} (payload label head result base types extras : OTerm alpha) (j : alpha → beta) :
    (StepNumberedPayload payload label head result base types extras).relabel j = StepNumberedPayload (payload.relabel j) (label.relabel j) (head.relabel j) (result.relabel j) (base.relabel j) (types.relabel j) (extras.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepNumberedPayload payload label head result base types extras).subst (fun a => emb (.var (j a))) = _
  rw [stepNumberedPayloadSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSyntaxProof
