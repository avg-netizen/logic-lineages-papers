module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
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
open OriginalTypedDecoderInternalRequestSyntaxProof


def stepPushOneFields ( out mode gamma typ raw rest : OTerm alpha) (ys : Fin 2 → OTerm alpha) : Formula alpha :=
  StepRequest (ys 0) mode gamma typ raw ⊓
    (StepCons (ys 1) (ys 0) rest ⊓ StepLive out (ys 1))

def stepPushOneMatrix (out mode gamma typ raw rest : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  stepPushOneFields (out.relabel Sum.inl) (mode.relabel Sum.inl) (gamma.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) (rest.relabel Sum.inl) (fun i => .var (.inr i))

theorem stepPushOneFieldsSubst {beta : Type} (out mode gamma typ raw rest : OTerm alpha)
    (ys : Fin 2 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stepPushOneFields out mode gamma typ raw rest ys).subst (fun a => emb (ts a)) =
      stepPushOneFields (out.subst ts) (mode.subst ts) (gamma.subst ts) (typ.subst ts) (raw.subst ts) (rest.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stepPushOneFields,conjunctionSubst,stepRequestSubst,stepConsSubst,stepLiveSubst]

theorem stepPushOneMatrixWitness (out mode gamma typ raw rest : OTerm alpha) (ys : Fin 2 → OTerm alpha) :
    (stepPushOneMatrix out mode gamma typ raw rest).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stepPushOneFields out mode gamma typ raw rest ys := by
  unfold stepPushOneMatrix
  rw [witnessEmbedding,stepPushOneFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stepPushOneIntro (out mode gamma typ raw rest : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepPushOneFields out mode gamma typ raw rest ys))) :
    Nonempty (Derivation body Delta (StepPushOne out mode gamma typ raw rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta
    (stepPushOneMatrix out mode gamma typ raw rest) (fun i => emb (ys i))
  rw [stepPushOneMatrixWitness]
  exact h

theorem stepPushOneCases (out mode gamma typ raw rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepPushOne out mode gamma typ raw rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 2 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stepPushOneFields (out.relabel j) (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (rest.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (stepPushOneMatrix out mode gamma typ raw rest) psi h
  apply step (alpha ⊕ Fin 2) Sum.inl
    (stepPushOneMatrix out mode gamma typ raw rest :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stepPushOneSubst {beta : Type} (out mode gamma typ raw rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepPushOne out mode gamma typ raw rest).subst (fun a => emb (ts a)) = StepPushOne (out.subst ts) (mode.subst ts) (gamma.subst ts) (typ.subst ts) (raw.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (stepPushOneMatrix out mode gamma typ raw rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stepPushOneMatrix
  simp only [stepPushOneFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepPushOneRename {beta : Type} (out mode gamma typ raw rest : OTerm alpha) (j : alpha → beta) :
    (StepPushOne out mode gamma typ raw rest).relabel j = StepPushOne (out.relabel j) (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepPushOne out mode gamma typ raw rest).subst (fun a => emb (.var (j a))) = _
  rw [stepPushOneSubst]
  simp only [← termRelabelAsSubst]

def stepPushTwoFields ( out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha) (ys : Fin 4 → OTerm alpha) : Formula alpha :=
  StepRequest (ys 0) mode₁ gamma₁ typ₁ raw₁ ⊓
    (StepRequest (ys 1) mode₂ gamma₂ typ₂ raw₂ ⊓
      (StepCons (ys 2) (ys 1) rest ⊓
        (StepCons (ys 3) (ys 0) (ys 2) ⊓ StepLive out (ys 3))))

def stepPushTwoMatrix (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  stepPushTwoFields (out.relabel Sum.inl) (mode₁.relabel Sum.inl) (gamma₁.relabel Sum.inl) (typ₁.relabel Sum.inl) (raw₁.relabel Sum.inl) (mode₂.relabel Sum.inl) (gamma₂.relabel Sum.inl) (typ₂.relabel Sum.inl) (raw₂.relabel Sum.inl) (rest.relabel Sum.inl) (fun i => .var (.inr i))

theorem stepPushTwoFieldsSubst {beta : Type} (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha)
    (ys : Fin 4 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stepPushTwoFields out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest ys).subst (fun a => emb (ts a)) =
      stepPushTwoFields (out.subst ts) (mode₁.subst ts) (gamma₁.subst ts) (typ₁.subst ts) (raw₁.subst ts) (mode₂.subst ts) (gamma₂.subst ts) (typ₂.subst ts) (raw₂.subst ts) (rest.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stepPushTwoFields,conjunctionSubst,stepRequestSubst,stepConsSubst,stepLiveSubst]

theorem stepPushTwoMatrixWitness (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha) (ys : Fin 4 → OTerm alpha) :
    (stepPushTwoMatrix out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stepPushTwoFields out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest ys := by
  unfold stepPushTwoMatrix
  rw [witnessEmbedding,stepPushTwoFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stepPushTwoIntro (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha) (ys : Fin 4 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stepPushTwoFields out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest ys))) :
    Nonempty (Derivation body Delta (StepPushTwo out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 4 Delta
    (stepPushTwoMatrix out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest) (fun i => emb (ys i))
  rw [stepPushTwoMatrixWitness]
  exact h

theorem stepPushTwoCases (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepPushTwo out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 4 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stepPushTwoFields (out.relabel j) (mode₁.relabel j) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) (mode₂.relabel j) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) (rest.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 4 Delta (stepPushTwoMatrix out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest) psi h
  apply step (alpha ⊕ Fin 4) Sum.inl
    (stepPushTwoMatrix out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stepPushTwoSubst {beta : Type} (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepPushTwo out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest).subst (fun a => emb (ts a)) = StepPushTwo (out.subst ts) (mode₁.subst ts) (gamma₁.subst ts) (typ₁.subst ts) (raw₁.subst ts) (mode₂.subst ts) (gamma₂.subst ts) (typ₂.subst ts) (raw₂.subst ts) (rest.subst ts) := by
  change (InternalFiniteBlocks.block (stepPushTwoMatrix out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stepPushTwoMatrix
  simp only [stepPushTwoFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stepPushTwoRename {beta : Type} (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha) (j : alpha → beta) :
    (StepPushTwo out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest).relabel j = StepPushTwo (out.relabel j) (mode₁.relabel j) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) (mode₂.relabel j) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepPushTwo out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest).subst (fun a => emb (.var (j a))) = _
  rw [stepPushTwoSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
