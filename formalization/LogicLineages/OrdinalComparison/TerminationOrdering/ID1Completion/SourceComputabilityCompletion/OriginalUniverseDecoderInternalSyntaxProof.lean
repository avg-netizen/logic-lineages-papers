module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalOriginalOrderSyntaxProof (notSubst)
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalUniverseDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem conditionSubst {beta : Type} (M W : Program 2)
    (mode typ tag domain numberedHead context : OTerm alpha) (ts : alpha → OTerm beta) :
    (guardCondition M W mode typ tag domain numberedHead context).subst (fun a => emb (ts a)) =
      guardCondition M W (mode.subst ts) (typ.subst ts) (tag.subst ts)
        (domain.subst ts) (numberedHead.subst ts) (context.subst ts) := by
  simp only [guardCondition,conjunctionSubst,orSubst,notSubst,equalSubst,numeralSubst,graph2,programSubst,consTermSubst,emptySubst]

@[simp] theorem conditionRename {beta : Type} (M W : Program 2)
    (mode typ tag domain numberedHead context : OTerm alpha) (j : alpha → beta) :
    (guardCondition M W mode typ tag domain numberedHead context).relabel j =
      guardCondition M W (mode.relabel j) (typ.relabel j) (tag.relabel j)
        (domain.relabel j) (numberedHead.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (guardCondition M W mode typ tag domain numberedHead context).subst (fun a => emb (.var (j a))) = _
  rw [conditionSubst]
  simp only [← termRelabelAsSubst]

def guardFields (M : Program 2) (W : Program 2) (out : OTerm alpha) (request : OTerm alpha) (context : OTerm alpha) (ys : Fin 10 → OTerm alpha) : Formula alpha :=
  StepRequest request (ys 0) (ys 1) (ys 2) (ys 3) ⊓
    (StepPair (ys 3) (ys 4) (ys 5) ⊓
      (StepPair (ys 5) (ys 6) (ys 7) ⊓
        (StepPair (ys 7) (ys 8) (ys 9) ⊓
          ((guardCondition M W (ys 0) (ys 2) (ys 4) (ys 6) (ys 8) context ⊓ equal out (numeral 1)) ⊔
            ((guardCondition M W (ys 0) (ys 2) (ys 4) (ys 6) (ys 8) context).not ⊓ equal out (numeral 0))))))

def guardMatrix (M : Program 2) (W : Program 2) (out : OTerm alpha) (request : OTerm alpha) (context : OTerm alpha) : Formula (alpha ⊕ Fin 10) :=
  guardFields M W (out.relabel Sum.inl) (request.relabel Sum.inl) (context.relabel Sum.inl) (fun i => .var (.inr i))

theorem guardFieldsSubst {beta : Type} (M : Program 2) (W : Program 2) (out : OTerm alpha) (request : OTerm alpha) (context : OTerm alpha)
    (ys : Fin 10 → OTerm alpha) (ts : alpha → OTerm beta) :
    (guardFields M W out request context ys).subst (fun a => emb (ts a)) =
      guardFields M W (out.subst ts) (request.subst ts) (context.subst ts) (fun i => (ys i).subst ts) := by
  simp only [guardFields,conjunctionSubst,orSubst,notSubst,equalSubst,numeralSubst,stepRequestSubst,stepPairSubst,conditionSubst]

theorem guardMatrixWitness (M : Program 2) (W : Program 2) (out : OTerm alpha) (request : OTerm alpha) (context : OTerm alpha) (ys : Fin 10 → OTerm alpha) :
    (guardMatrix M W out request context).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      guardFields M W out request context ys := by
  unfold guardMatrix
  rw [witnessEmbedding,guardFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem guardIntro (M : Program 2) (W : Program 2) (out : OTerm alpha) (request : OTerm alpha) (context : OTerm alpha) (ys : Fin 10 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (guardFields M W out request context ys))) :
    Nonempty (Derivation body Delta (guardSpec M W out request context)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 10 Delta
    (guardMatrix M W out request context) (fun i => emb (ys i))
  rw [guardMatrixWitness]
  exact h

theorem guardCases (M : Program 2) (W : Program 2) (out : OTerm alpha) (request : OTerm alpha) (context : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (guardSpec M W out request context)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 10 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (guardFields M W (out.relabel j) (request.relabel j) (context.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 10 Delta (guardMatrix M W out request context) psi h
  apply step (alpha ⊕ Fin 10) Sum.inl
    (guardMatrix M W out request context :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem guardSubst {beta : Type} (M : Program 2) (W : Program 2) (out : OTerm alpha) (request : OTerm alpha) (context : OTerm alpha) (ts : alpha → OTerm beta) :
    (guardSpec M W out request context).subst (fun a => emb (ts a)) = guardSpec M W (out.subst ts) (request.subst ts) (context.subst ts) := by
  change (InternalFiniteBlocks.block (guardMatrix M W out request context)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold guardMatrix
  simp only [guardFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem guardRename {beta : Type} (M : Program 2) (W : Program 2) (out : OTerm alpha) (request : OTerm alpha) (context : OTerm alpha) (j : alpha → beta) :
    (guardSpec M W out request context).relabel j = guardSpec M W (out.relabel j) (request.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (guardSpec M W out request context).subst (fun a => emb (.var (j a))) = _
  rw [guardSubst]
  simp only [← termRelabelAsSubst]

def nonemptyFields (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (work : OTerm alpha) (context : OTerm alpha) (ys : Fin 2 → OTerm alpha) : Formula alpha :=
  StepCons work (ys 0) (ys 1) ⊓
    ((guardSpec M W (numeral 1) (ys 0) context ⊓ OriginalTypedDecoderStepSpecification.stepSpec H out input) ⊔
      ((guardSpec M W (numeral 1) (ys 0) context).not ⊓ equal out (numeral 0)))

def nonemptyMatrix (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (work : OTerm alpha) (context : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  nonemptyFields H M W (out.relabel Sum.inl) (input.relabel Sum.inl) (work.relabel Sum.inl) (context.relabel Sum.inl) (fun i => .var (.inr i))

theorem nonemptyFieldsSubst {beta : Type} (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (work : OTerm alpha) (context : OTerm alpha)
    (ys : Fin 2 → OTerm alpha) (ts : alpha → OTerm beta) :
    (nonemptyFields H M W out input work context ys).subst (fun a => emb (ts a)) =
      nonemptyFields H M W (out.subst ts) (input.subst ts) (work.subst ts) (context.subst ts) (fun i => (ys i).subst ts) := by
  simp only [nonemptyFields,conjunctionSubst,orSubst,notSubst,equalSubst,numeralSubst,stepConsSubst,guardSubst,OriginalTypedDecoderInternalStateSyntaxProof.stateSubst]

theorem nonemptyMatrixWitness (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (work : OTerm alpha) (context : OTerm alpha) (ys : Fin 2 → OTerm alpha) :
    (nonemptyMatrix H M W out input work context).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      nonemptyFields H M W out input work context ys := by
  unfold nonemptyMatrix
  rw [witnessEmbedding,nonemptyFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem nonemptyIntro (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (work : OTerm alpha) (context : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (nonemptyFields H M W out input work context ys))) :
    Nonempty (Derivation body Delta (nonemptySpec H M W out input work context)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta
    (nonemptyMatrix H M W out input work context) (fun i => emb (ys i))
  rw [nonemptyMatrixWitness]
  exact h

theorem nonemptyCases (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (work : OTerm alpha) (context : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (nonemptySpec H M W out input work context)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 2 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (nonemptyFields H M W (out.relabel j) (input.relabel j) (work.relabel j) (context.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (nonemptyMatrix H M W out input work context) psi h
  apply step (alpha ⊕ Fin 2) Sum.inl
    (nonemptyMatrix H M W out input work context :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem nonemptySubst {beta : Type} (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (work : OTerm alpha) (context : OTerm alpha) (ts : alpha → OTerm beta) :
    (nonemptySpec H M W out input work context).subst (fun a => emb (ts a)) = nonemptySpec H M W (out.subst ts) (input.subst ts) (work.subst ts) (context.subst ts) := by
  change (InternalFiniteBlocks.block (nonemptyMatrix H M W out input work context)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold nonemptyMatrix
  simp only [nonemptyFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem nonemptyRename {beta : Type} (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (work : OTerm alpha) (context : OTerm alpha) (j : alpha → beta) :
    (nonemptySpec H M W out input work context).relabel j = nonemptySpec H M W (out.relabel j) (input.relabel j) (work.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (nonemptySpec H M W out input work context).subst (fun a => emb (.var (j a))) = _
  rw [nonemptySubst]
  simp only [← termRelabelAsSubst]

def stateFields (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (context : OTerm alpha) (ys : Fin 2 → OTerm alpha) : Formula alpha :=
  StepPair input (ys 0) (ys 1) ⊓
    (((equal (ys 0) (numeral 1)).not ⊓ equal out (numeral 0)) ⊔
      (equal (ys 0) (numeral 1) ⊓
        ((equal (ys 1) (numeral 0) ⊓ equal out input) ⊔
          ((equal (ys 1) (numeral 0)).not ⊓ nonemptySpec H M W out input (ys 1) context))))

def stateMatrix (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (context : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  stateFields H M W (out.relabel Sum.inl) (input.relabel Sum.inl) (context.relabel Sum.inl) (fun i => .var (.inr i))

theorem stateFieldsSubst {beta : Type} (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (context : OTerm alpha)
    (ys : Fin 2 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stateFields H M W out input context ys).subst (fun a => emb (ts a)) =
      stateFields H M W (out.subst ts) (input.subst ts) (context.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stateFields,conjunctionSubst,orSubst,notSubst,equalSubst,numeralSubst,stepPairSubst,nonemptySubst]

theorem stateMatrixWitness (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (context : OTerm alpha) (ys : Fin 2 → OTerm alpha) :
    (stateMatrix H M W out input context).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stateFields H M W out input context ys := by
  unfold stateMatrix
  rw [witnessEmbedding,stateFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stateIntro (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (context : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stateFields H M W out input context ys))) :
    Nonempty (Derivation body Delta (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input context)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta
    (stateMatrix H M W out input context) (fun i => emb (ys i))
  rw [stateMatrixWitness]
  exact h

theorem stateCases (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (context : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input context)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 2 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stateFields H M W (out.relabel j) (input.relabel j) (context.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (stateMatrix H M W out input context) psi h
  apply step (alpha ⊕ Fin 2) Sum.inl
    (stateMatrix H M W out input context :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stateSubst {beta : Type} (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (context : OTerm alpha) (ts : alpha → OTerm beta) :
    (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input context).subst (fun a => emb (ts a)) = OriginalUniverseDecoderStepSpecification.stepSpec H M W (out.subst ts) (input.subst ts) (context.subst ts) := by
  change (InternalFiniteBlocks.block (stateMatrix H M W out input context)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stateMatrix
  simp only [stateFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stateRename {beta : Type} (H : Program 1) (M : Program 2) (W : Program 2) (out : OTerm alpha) (input : OTerm alpha) (context : OTerm alpha) (j : alpha → beta) :
    (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input context).relabel j = OriginalUniverseDecoderStepSpecification.stepSpec H M W (out.relabel j) (input.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (OriginalUniverseDecoderStepSpecification.stepSpec H M W out input context).subst (fun a => emb (.var (j a))) = _
  rw [stateSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalSyntaxProof
