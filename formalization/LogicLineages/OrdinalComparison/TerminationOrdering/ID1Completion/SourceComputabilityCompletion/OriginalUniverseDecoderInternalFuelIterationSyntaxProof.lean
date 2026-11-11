module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb eqnSubst sucSubst zSubst sucRelabel zRelabel)
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (WorkFuelGraph Terminal)
open OriginalTypedDecoderInternalFuelIterationSyntaxProof (terminalSubst terminalRename workFuelSubst)
open OriginalTypedDecoderInternalScalarSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def runFields {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (out count workCode state c : OTerm alpha) : Formula alpha :=
  StepLive state workCode ⊓ graph3 (iterate H M contextWindow) out count state c

def runMatrix {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (out count workCode c : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  runFields H M contextWindow (out.relabel Sum.inl) (count.relabel Sum.inl)
    (workCode.relabel Sum.inl) (.var (.inr 0)) (c.relabel Sum.inl)

theorem runFieldsSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (out count workCode state c : OTerm alpha) (ts : alpha → OTerm beta) :
    (runFields H M contextWindow out count workCode state c).subst (fun a => emb (ts a)) =
      runFields H M contextWindow (out.subst ts) (count.subst ts) (workCode.subst ts) (state.subst ts) (c.subst ts) := by
  simp only [runFields,conjunctionSubst,stepLiveSubst,graph3,programSubst,
    consTermSubst,emptySubst]

theorem runMatrixWitness {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (out count workCode state c : OTerm alpha) :
    (runMatrix H M contextWindow out count workCode c).subst
      (Sum.elim Term.var (fun i => emb ((![state] : Fin 1 → OTerm alpha) i))) =
      runFields H M contextWindow out count workCode state c := by
  unfold runMatrix
  rw [witnessEmbedding,runFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem workRunSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (out count workCode c : OTerm alpha) (ts : alpha → OTerm beta) :
    (WorkRun H M contextWindow out count workCode c).subst (fun a => emb (ts a)) =
      WorkRun H M contextWindow (out.subst ts) (count.subst ts) (workCode.subst ts) (c.subst ts) := by
  change (InternalFiniteBlocks.block (runMatrix H M contextWindow out count workCode c)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold runMatrix
  simp only [runFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem workRunRename {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (out count workCode c : OTerm alpha) (j : alpha → beta) :
    (WorkRun H M contextWindow out count workCode c).relabel j =
      WorkRun H M contextWindow (out.relabel j) (count.relabel j) (workCode.relabel j) (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (WorkRun H M contextWindow out count workCode c).subst (fun a => emb (.var (j a))) = _
  rw [workRunSubst]
  simp only [← termRelabelAsSubst]

theorem successfulWorkSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode c : OTerm alpha) (ts : alpha → OTerm beta) :
    (SuccessfulWork H M contextWindow count workCode c).subst (fun a => emb (ts a)) =
      SuccessfulWork H M contextWindow (count.subst ts) (workCode.subst ts) (c.subst ts) := by
  simp only [SuccessfulWork,workRunSubst,numeral,sucSubst,zSubst]

@[simp] theorem successfulWorkRename {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode c : OTerm alpha) (j : alpha → beta) :
    (SuccessfulWork H M contextWindow count workCode c).relabel j =
      SuccessfulWork H M contextWindow (count.relabel j) (workCode.relabel j) (c.relabel j) := by
  simp only [SuccessfulWork,workRunRename,numeral,sucRelabel,zRelabel]

def terminatedFields {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode out c : OTerm alpha) : Formula alpha :=
  WorkRun H M contextWindow out count workCode c ⊓ Terminal out

def terminatedMatrix {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode c : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  terminatedFields H M contextWindow (count.relabel Sum.inl) (workCode.relabel Sum.inl) (.var (.inr 0)) (c.relabel Sum.inl)

theorem terminatedFieldsSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode out c : OTerm alpha) (ts : alpha → OTerm beta) :
    (terminatedFields H M contextWindow count workCode out c).subst (fun a => emb (ts a)) =
      terminatedFields H M contextWindow (count.subst ts) (workCode.subst ts) (out.subst ts) (c.subst ts) := by
  simp only [terminatedFields,conjunctionSubst,workRunSubst,terminalSubst]

theorem terminatedMatrixWitness {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode out c : OTerm alpha) :
    (terminatedMatrix H M contextWindow count workCode c).subst
      (Sum.elim Term.var (fun i => emb ((![out] : Fin 1 → OTerm alpha) i))) =
      terminatedFields H M contextWindow count workCode out c := by
  unfold terminatedMatrix
  rw [witnessEmbedding,terminatedFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem terminatedWorkSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode c : OTerm alpha) (ts : alpha → OTerm beta) :
    (TerminatedWork H M contextWindow count workCode c).subst (fun a => emb (ts a)) =
      TerminatedWork H M contextWindow (count.subst ts) (workCode.subst ts) (c.subst ts) := by
  change (InternalFiniteBlocks.block (terminatedMatrix H M contextWindow count workCode c)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold terminatedMatrix
  simp only [terminatedFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem terminatedWorkRename {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode c : OTerm alpha) (j : alpha → beta) :
    (TerminatedWork H M contextWindow count workCode c).relabel j =
      TerminatedWork H M contextWindow (count.relabel j) (workCode.relabel j) (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (TerminatedWork H M contextWindow count workCode c).subst (fun a => emb (.var (j a))) = _
  rw [terminatedWorkSubst]
  simp only [← termRelabelAsSubst]

def acceptedFields {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (workCode count c : OTerm alpha) : Formula alpha :=
  WorkFuelGraph count workCode ⊓ SuccessfulWork H M contextWindow count workCode c

def acceptedMatrix {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (workCode c : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  acceptedFields H M contextWindow (workCode.relabel Sum.inl) (.var (.inr 0)) (c.relabel Sum.inl)

theorem acceptedFieldsSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (workCode count c : OTerm alpha) (ts : alpha → OTerm beta) :
    (acceptedFields H M contextWindow workCode count c).subst (fun a => emb (ts a)) =
      acceptedFields H M contextWindow (workCode.subst ts) (count.subst ts) (c.subst ts) := by
  simp only [acceptedFields,conjunctionSubst,workFuelSubst,successfulWorkSubst]

theorem acceptedMatrixWitness {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (workCode count c : OTerm alpha) :
    (acceptedMatrix H M contextWindow workCode c).subst
      (Sum.elim Term.var (fun i => emb ((![count] : Fin 1 → OTerm alpha) i))) =
      acceptedFields H M contextWindow workCode count c := by
  unfold acceptedMatrix
  rw [witnessEmbedding,acceptedFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem workAcceptedSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (workCode c : OTerm alpha) (ts : alpha → OTerm beta) :
    (WorkAccepted H M contextWindow workCode c).subst (fun a => emb (ts a)) =
      WorkAccepted H M contextWindow (workCode.subst ts) (c.subst ts) := by
  change (InternalFiniteBlocks.block (acceptedMatrix H M contextWindow workCode c)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold acceptedMatrix
  simp only [acceptedFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem workAcceptedRename {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (workCode c : OTerm alpha) (j : alpha → beta) :
    (WorkAccepted H M contextWindow workCode c).relabel j = WorkAccepted H M contextWindow (workCode.relabel j) (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (WorkAccepted H M contextWindow workCode c).subst (fun a => emb (.var (j a))) = _
  rw [workAcceptedSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSyntaxProof
