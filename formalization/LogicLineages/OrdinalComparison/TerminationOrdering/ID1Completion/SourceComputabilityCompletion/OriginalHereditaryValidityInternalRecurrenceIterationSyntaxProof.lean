module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
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
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalPushSyntaxProof
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

def runFields {alpha : Type} (s t m : Program 2)
    (out count workCode state : OTerm alpha) : Formula alpha :=
  StateGraph state (numeral 1) workCode ⊓ graph2 (iterate s t m) out count state

def runMatrix {alpha : Type} (s t m : Program 2)
    (out count workCode : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  runFields s t m (out.relabel Sum.inl) (count.relabel Sum.inl)
    (workCode.relabel Sum.inl) (.var (.inr 0))

theorem runFieldsSubst {alpha beta : Type} (s t m : Program 2)
    (out count workCode state : OTerm alpha) (ts : alpha → OTerm beta) :
    (runFields s t m out count workCode state).subst (fun a => emb (ts a)) =
      runFields s t m (out.subst ts) (count.subst ts) (workCode.subst ts) (state.subst ts) := by
  simp only [runFields,StateGraph,conjunctionSubst,graph2,programSubst,
    consTermSubst,emptySubst,numeral,sucSubst,zSubst]

theorem runMatrixWitness {alpha : Type} (s t m : Program 2)
    (out count workCode state : OTerm alpha) :
    (runMatrix s t m out count workCode).subst
      (Sum.elim Term.var (fun i => emb ((![state] : Fin 1 → OTerm alpha) i))) =
      runFields s t m out count workCode state := by
  unfold runMatrix
  rw [witnessEmbedding,runFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem workRunSubst {alpha beta : Type} (s t m : Program 2)
    (out count workCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (WorkRun s t m out count workCode).subst (fun a => emb (ts a)) =
      WorkRun s t m (out.subst ts) (count.subst ts) (workCode.subst ts) := by
  change (InternalFiniteBlocks.block (runMatrix s t m out count workCode)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold runMatrix
  simp only [runFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem workRunRename {alpha beta : Type} (s t m : Program 2)
    (out count workCode : OTerm alpha) (j : alpha → beta) :
    (WorkRun s t m out count workCode).relabel j =
      WorkRun s t m (out.relabel j) (count.relabel j) (workCode.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (WorkRun s t m out count workCode).subst (fun a => emb (.var (j a))) = _
  rw [workRunSubst]
  simp only [← termRelabelAsSubst]

theorem successfulWorkSubst {alpha beta : Type} (s t m : Program 2)
    (count workCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (SuccessfulWork s t m count workCode).subst (fun a => emb (ts a)) =
      SuccessfulWork s t m (count.subst ts) (workCode.subst ts) := by
  simp only [SuccessfulWork,workRunSubst,numeral,sucSubst,zSubst]

@[simp] theorem successfulWorkRename {alpha beta : Type} (s t m : Program 2)
    (count workCode : OTerm alpha) (j : alpha → beta) :
    (SuccessfulWork s t m count workCode).relabel j =
      SuccessfulWork s t m (count.relabel j) (workCode.relabel j) := by
  simp only [SuccessfulWork,workRunRename,numeral,sucRelabel,zRelabel]

def terminatedFields {alpha : Type} (s t m : Program 2)
    (count workCode out : OTerm alpha) : Formula alpha :=
  WorkRun s t m out count workCode ⊓ Terminal out

def terminatedMatrix {alpha : Type} (s t m : Program 2)
    (count workCode : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  terminatedFields s t m (count.relabel Sum.inl) (workCode.relabel Sum.inl) (.var (.inr 0))

theorem terminatedFieldsSubst {alpha beta : Type} (s t m : Program 2)
    (count workCode out : OTerm alpha) (ts : alpha → OTerm beta) :
    (terminatedFields s t m count workCode out).subst (fun a => emb (ts a)) =
      terminatedFields s t m (count.subst ts) (workCode.subst ts) (out.subst ts) := by
  simp only [terminatedFields,conjunctionSubst,workRunSubst,terminalSubst]

theorem terminatedMatrixWitness {alpha : Type} (s t m : Program 2)
    (count workCode out : OTerm alpha) :
    (terminatedMatrix s t m count workCode).subst
      (Sum.elim Term.var (fun i => emb ((![out] : Fin 1 → OTerm alpha) i))) =
      terminatedFields s t m count workCode out := by
  unfold terminatedMatrix
  rw [witnessEmbedding,terminatedFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem terminatedWorkSubst {alpha beta : Type} (s t m : Program 2)
    (count workCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (TerminatedWork s t m count workCode).subst (fun a => emb (ts a)) =
      TerminatedWork s t m (count.subst ts) (workCode.subst ts) := by
  change (InternalFiniteBlocks.block (terminatedMatrix s t m count workCode)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold terminatedMatrix
  simp only [terminatedFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem terminatedWorkRename {alpha beta : Type} (s t m : Program 2)
    (count workCode : OTerm alpha) (j : alpha → beta) :
    (TerminatedWork s t m count workCode).relabel j =
      TerminatedWork s t m (count.relabel j) (workCode.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (TerminatedWork s t m count workCode).subst (fun a => emb (.var (j a))) = _
  rw [terminatedWorkSubst]
  simp only [← termRelabelAsSubst]

theorem workFuelSubst {alpha beta : Type} (count workCode : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (WorkFuelGraph count workCode).subst (fun a => emb (ts a)) =
      WorkFuelGraph (count.subst ts) (workCode.subst ts) := by
  simp only [WorkFuelGraph,graph1,programSubst,consTermSubst,emptySubst]

def acceptedFields {alpha : Type} (s t m : Program 2)
    (workCode count : OTerm alpha) : Formula alpha :=
  WorkFuelGraph count workCode ⊓ SuccessfulWork s t m count workCode

def acceptedMatrix {alpha : Type} (s t m : Program 2)
    (workCode : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  acceptedFields s t m (workCode.relabel Sum.inl) (.var (.inr 0))

theorem acceptedFieldsSubst {alpha beta : Type} (s t m : Program 2)
    (workCode count : OTerm alpha) (ts : alpha → OTerm beta) :
    (acceptedFields s t m workCode count).subst (fun a => emb (ts a)) =
      acceptedFields s t m (workCode.subst ts) (count.subst ts) := by
  simp only [acceptedFields,conjunctionSubst,workFuelSubst,successfulWorkSubst]

theorem acceptedMatrixWitness {alpha : Type} (s t m : Program 2)
    (workCode count : OTerm alpha) :
    (acceptedMatrix s t m workCode).subst
      (Sum.elim Term.var (fun i => emb ((![count] : Fin 1 → OTerm alpha) i))) =
      acceptedFields s t m workCode count := by
  unfold acceptedMatrix
  rw [witnessEmbedding,acceptedFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem workAcceptedSubst {alpha beta : Type} (s t m : Program 2)
    (workCode : OTerm alpha) (ts : alpha → OTerm beta) :
    (WorkAccepted s t m workCode).subst (fun a => emb (ts a)) =
      WorkAccepted s t m (workCode.subst ts) := by
  change (InternalFiniteBlocks.block (acceptedMatrix s t m workCode)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold acceptedMatrix
  simp only [acceptedFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem workAcceptedRename {alpha beta : Type} (s t m : Program 2)
    (workCode : OTerm alpha) (j : alpha → beta) :
    (WorkAccepted s t m workCode).relabel j = WorkAccepted s t m (workCode.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (WorkAccepted s t m workCode).subst (fun a => emb (.var (j a))) = _
  rw [workAcceptedSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
