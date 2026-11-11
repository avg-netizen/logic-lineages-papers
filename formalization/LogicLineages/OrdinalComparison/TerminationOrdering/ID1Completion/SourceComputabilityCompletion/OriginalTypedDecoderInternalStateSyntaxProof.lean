module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateSyntaxProof
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
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalBinarySyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open InternalOriginalOrderSyntaxProof (notSubst)


open OriginalTypedDecoderInternalDispatchSyntaxProof

def nonemptyFields (H : Program 1) (out work : OTerm alpha) (ys : Fin 8 → OTerm alpha) : Formula alpha :=
  StepCons work (ys 0) (ys 1) ⊓
    (StepRequest (ys 0) (ys 2) (ys 3) (ys 4) (ys 5) ⊓
      (StepPair (ys 5) (ys 6) (ys 7) ⊓
        StepModeDispatch H out (ys 2) (ys 3) (ys 4) (ys 6) (ys 7) (ys 1)))

def nonemptyMatrix (H : Program 1) (out work : OTerm alpha) : Formula (alpha ⊕ Fin 8) :=
  nonemptyFields H (out.relabel Sum.inl) (work.relabel Sum.inl) (fun i => .var (.inr i))

theorem nonemptyFieldsSubst {beta : Type} (H : Program 1) (out work : OTerm alpha)
    (ys : Fin 8 → OTerm alpha) (ts : alpha → OTerm beta) :
    (nonemptyFields H out work ys).subst (fun x => emb (ts x)) =
      nonemptyFields H (out.subst ts) (work.subst ts) (fun i => (ys i).subst ts) := by
  simp only [nonemptyFields,conjunctionSubst,stepConsSubst,stepRequestSubst,stepPairSubst,stepModeDispatchSubst]

theorem nonemptyMatrixWitness (H : Program 1) (out work : OTerm alpha) (ys : Fin 8 → OTerm alpha) :
    (nonemptyMatrix H out work).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      nonemptyFields H out work ys := by
  unfold nonemptyMatrix
  rw [witnessEmbedding,nonemptyFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem nonemptyIntro (H : Program 1) (out work : OTerm alpha) (ys : Fin 8 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (nonemptyFields H out work ys))) :
    Nonempty (Derivation body Delta (StepNonemptyWork H out work)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 8 Delta
    (nonemptyMatrix H out work) (fun i => emb (ys i))
  rw [nonemptyMatrixWitness]
  exact h

theorem nonemptyCases (H : Program 1) (out work : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepNonemptyWork H out work)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 8 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (nonemptyFields H (out.relabel j) (work.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 8 Delta (nonemptyMatrix H out work) psi h
  apply step (alpha ⊕ Fin 8) Sum.inl
    (nonemptyMatrix H out work :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem nonemptySubst {beta : Type} (H : Program 1) (out work : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepNonemptyWork H out work).subst (fun x => emb (ts x)) = StepNonemptyWork H (out.subst ts) (work.subst ts) := by
  change (InternalFiniteBlocks.block (nonemptyMatrix H out work)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold nonemptyMatrix
  simp only [nonemptyFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem nonemptyRename {beta : Type} (H : Program 1) (out work : OTerm alpha) (j : alpha → beta) :
    (StepNonemptyWork H out work).relabel j = StepNonemptyWork H (out.relabel j) (work.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepNonemptyWork H out work).subst (fun x => emb (.var (j x))) = _
  rw [nonemptySubst]
  simp only [← termRelabelAsSubst]

def stateFields (H : Program 1) (out input : OTerm alpha) (ys : Fin 2 → OTerm alpha) : Formula alpha :=
  StepPair input (ys 0) (ys 1) ⊓
    (((equal (ys 0) (numeral 1)).not ⊓ equal out (numeral 0)) ⊔
      (equal (ys 0) (numeral 1) ⊓
        ((equal (ys 1) (numeral 0) ⊓ equal out input) ⊔
          ((equal (ys 1) (numeral 0)).not ⊓ StepNonemptyWork H out (ys 1)))))

def stateMatrix (H : Program 1) (out input : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  stateFields H (out.relabel Sum.inl) (input.relabel Sum.inl) (fun i => .var (.inr i))

theorem stateFieldsSubst {beta : Type} (H : Program 1) (out input : OTerm alpha)
    (ys : Fin 2 → OTerm alpha) (ts : alpha → OTerm beta) :
    (stateFields H out input ys).subst (fun x => emb (ts x)) =
      stateFields H (out.subst ts) (input.subst ts) (fun i => (ys i).subst ts) := by
  simp only [stateFields,conjunctionSubst,stepPairSubst,nonemptySubst,orSubst,notSubst,equalSubst,numeralSubst]

theorem stateMatrixWitness (H : Program 1) (out input : OTerm alpha) (ys : Fin 2 → OTerm alpha) :
    (stateMatrix H out input).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      stateFields H out input ys := by
  unfold stateMatrix
  rw [witnessEmbedding,stateFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem stateIntro (H : Program 1) (out input : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (stateFields H out input ys))) :
    Nonempty (Derivation body Delta (stepSpec H out input)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta
    (stateMatrix H out input) (fun i => emb (ys i))
  rw [stateMatrixWitness]
  exact h

theorem stateCases (H : Program 1) (out input : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (stepSpec H out input)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (ys : Fin 2 → OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (stateFields H (out.relabel j) (input.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (stateMatrix H out input) psi h
  apply step (alpha ⊕ Fin 2) Sum.inl
    (stateMatrix H out input :: Delta.map (fun p => p.relabel Sum.inl))
    (fun i => .var (.inr i))
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem stateSubst {beta : Type} (H : Program 1) (out input : OTerm alpha) (ts : alpha → OTerm beta) :
    (stepSpec H out input).subst (fun x => emb (ts x)) = stepSpec H (out.subst ts) (input.subst ts) := by
  change (InternalFiniteBlocks.block (stateMatrix H out input)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stateMatrix
  simp only [stateFieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem stateRename {beta : Type} (H : Program 1) (out input : OTerm alpha) (j : alpha → beta) :
    (stepSpec H out input).relabel j = stepSpec H (out.relabel j) (input.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (stepSpec H out input).subst (fun x => emb (.var (j x))) = _
  rw [stateSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateSyntaxProof
