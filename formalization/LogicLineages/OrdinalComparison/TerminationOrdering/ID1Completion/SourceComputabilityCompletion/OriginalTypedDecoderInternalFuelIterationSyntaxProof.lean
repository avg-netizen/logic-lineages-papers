module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSyntaxProof
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
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalScalarSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem terminalSubst {alpha beta : Type} (state : OTerm alpha) (ts : alpha → OTerm beta) :
    (Terminal state).subst (fun a => emb (ts a)) = Terminal (state.subst ts) := by
  change ((equal state OrdinaryArithmetic.zeroTerm).subst (fun a => emb (ts a)) ⊔
    (equal state (numeral 2)).subst (fun a => emb (ts a))) = _
  simp only [Terminal,equalEqn,eqnSubst,numeral,sucSubst,zSubst]

@[simp] theorem terminalRename {alpha beta : Type} (state : OTerm alpha) (j : alpha → beta) :
    (Terminal state).relabel j = Terminal (state.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Terminal state).subst (fun a => emb (.var (j a))) = _
  rw [terminalSubst]
  simp only [← termRelabelAsSubst]

def runFields {alpha : Type} (H : Program 1)
    (out count workCode state : OTerm alpha) : Formula alpha :=
  StepLive state workCode ⊓ graph2 (iterate H) out count state

def runMatrix {alpha : Type} (H : Program 1)
    (out count workCode : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  runFields H (out.relabel Sum.inl) (count.relabel Sum.inl)
    (workCode.relabel Sum.inl) (.var (.inr 0))

theorem runFieldsSubst {alpha beta : Type} (H : Program 1)
    (out count workCode state : OTerm alpha) (ts : alpha → OTerm beta) :
    (runFields H out count workCode state).subst (fun a => emb (ts a)) =
      runFields H (out.subst ts) (count.subst ts) (workCode.subst ts) (state.subst ts) := by
  simp only [runFields,conjunctionSubst,stepLiveSubst,graph2,programSubst,
    consTermSubst,emptySubst]

theorem runMatrixWitness {alpha : Type} (H : Program 1)
    (out count workCode state : OTerm alpha) :
    (runMatrix H out count workCode).subst
      (Sum.elim Term.var (fun i => emb ((![state] : Fin 1 → OTerm alpha) i))) =
      runFields H out count workCode state := by
  unfold runMatrix
  rw [witnessEmbedding,runFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem workRunSubst {alpha beta : Type} (H : Program 1)
    (out count workCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (WorkRun H out count workCode).subst (fun a => emb (ts a)) =
      WorkRun H (out.subst ts) (count.subst ts) (workCode.subst ts) := by
  change (InternalFiniteBlocks.block (runMatrix H out count workCode)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold runMatrix
  simp only [runFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem workRunRename {alpha beta : Type} (H : Program 1)
    (out count workCode : OTerm alpha) (j : alpha → beta) :
    (WorkRun H out count workCode).relabel j =
      WorkRun H (out.relabel j) (count.relabel j) (workCode.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (WorkRun H out count workCode).subst (fun a => emb (.var (j a))) = _
  rw [workRunSubst]
  simp only [← termRelabelAsSubst]

theorem successfulWorkSubst {alpha beta : Type} (H : Program 1)
    (count workCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (SuccessfulWork H count workCode).subst (fun a => emb (ts a)) =
      SuccessfulWork H (count.subst ts) (workCode.subst ts) := by
  simp only [SuccessfulWork,workRunSubst,numeral,sucSubst,zSubst]

@[simp] theorem successfulWorkRename {alpha beta : Type} (H : Program 1)
    (count workCode : OTerm alpha) (j : alpha → beta) :
    (SuccessfulWork H count workCode).relabel j =
      SuccessfulWork H (count.relabel j) (workCode.relabel j) := by
  simp only [SuccessfulWork,workRunRename,numeral,sucRelabel,zRelabel]

def terminatedFields {alpha : Type} (H : Program 1)
    (count workCode out : OTerm alpha) : Formula alpha :=
  WorkRun H out count workCode ⊓ Terminal out

def terminatedMatrix {alpha : Type} (H : Program 1)
    (count workCode : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  terminatedFields H (count.relabel Sum.inl) (workCode.relabel Sum.inl) (.var (.inr 0))

theorem terminatedFieldsSubst {alpha beta : Type} (H : Program 1)
    (count workCode out : OTerm alpha) (ts : alpha → OTerm beta) :
    (terminatedFields H count workCode out).subst (fun a => emb (ts a)) =
      terminatedFields H (count.subst ts) (workCode.subst ts) (out.subst ts) := by
  simp only [terminatedFields,conjunctionSubst,workRunSubst,terminalSubst]

theorem terminatedMatrixWitness {alpha : Type} (H : Program 1)
    (count workCode out : OTerm alpha) :
    (terminatedMatrix H count workCode).subst
      (Sum.elim Term.var (fun i => emb ((![out] : Fin 1 → OTerm alpha) i))) =
      terminatedFields H count workCode out := by
  unfold terminatedMatrix
  rw [witnessEmbedding,terminatedFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem terminatedWorkSubst {alpha beta : Type} (H : Program 1)
    (count workCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (TerminatedWork H count workCode).subst (fun a => emb (ts a)) =
      TerminatedWork H (count.subst ts) (workCode.subst ts) := by
  change (InternalFiniteBlocks.block (terminatedMatrix H count workCode)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold terminatedMatrix
  simp only [terminatedFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem terminatedWorkRename {alpha beta : Type} (H : Program 1)
    (count workCode : OTerm alpha) (j : alpha → beta) :
    (TerminatedWork H count workCode).relabel j =
      TerminatedWork H (count.relabel j) (workCode.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (TerminatedWork H count workCode).subst (fun a => emb (.var (j a))) = _
  rw [terminatedWorkSubst]
  simp only [← termRelabelAsSubst]

theorem workFuelSubst {alpha beta : Type} (count workCode : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (WorkFuelGraph count workCode).subst (fun a => emb (ts a)) =
      WorkFuelGraph (count.subst ts) (workCode.subst ts) := by
  simp only [WorkFuelGraph,graph1,programSubst,consTermSubst,emptySubst]

def acceptedFields {alpha : Type} (H : Program 1)
    (workCode count : OTerm alpha) : Formula alpha :=
  WorkFuelGraph count workCode ⊓ SuccessfulWork H count workCode

def acceptedMatrix {alpha : Type} (H : Program 1)
    (workCode : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  acceptedFields H (workCode.relabel Sum.inl) (.var (.inr 0))

theorem acceptedFieldsSubst {alpha beta : Type} (H : Program 1)
    (workCode count : OTerm alpha) (ts : alpha → OTerm beta) :
    (acceptedFields H workCode count).subst (fun a => emb (ts a)) =
      acceptedFields H (workCode.subst ts) (count.subst ts) := by
  simp only [acceptedFields,conjunctionSubst,workFuelSubst,successfulWorkSubst]

theorem acceptedMatrixWitness {alpha : Type} (H : Program 1)
    (workCode count : OTerm alpha) :
    (acceptedMatrix H workCode).subst
      (Sum.elim Term.var (fun i => emb ((![count] : Fin 1 → OTerm alpha) i))) =
      acceptedFields H workCode count := by
  unfold acceptedMatrix
  rw [witnessEmbedding,acceptedFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem workAcceptedSubst {alpha beta : Type} (H : Program 1)
    (workCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (WorkAccepted H workCode).subst (fun a => emb (ts a)) =
      WorkAccepted H (workCode.subst ts) := by
  change (InternalFiniteBlocks.block (acceptedMatrix H workCode)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold acceptedMatrix
  simp only [acceptedFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem workAcceptedRename {alpha beta : Type} (H : Program 1)
    (workCode : OTerm alpha) (j : alpha → beta) :
    (WorkAccepted H workCode).relabel j = WorkAccepted H (workCode.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (WorkAccepted H workCode).subst (fun a => emb (.var (j a))) = _
  rw [workAcceptedSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSyntaxProof
