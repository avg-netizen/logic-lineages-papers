module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingPushProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
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
open InternalApplicationValidityStackAppendSyntaxProof InternalRawListRecursionSyntaxProof
open InternalGraphCompositionSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof OriginalTypedDecoderInternalDispatchSyntaxProof
open OriginalTypedDecoderInternalVariableSyntaxProof OriginalTypedDecoderInternalLambdaSyntaxProof
open OriginalTypedDecoderInternalApplicationSyntaxProof OriginalTypedDecoderInternalOrdinarySyntaxProof
open OriginalTypedDecoderInternalNumberedSyntaxProof OriginalTypedDecoderInternalConsSyntaxProof

/-- The original eight local clauses and the original three dispatch clauses. -/
inductive Kind where
  | variable | lambda | application | bottom | ordinary | numbered | nil | cons
  | terms | arguments | modes

def LocalSpec (H : Program 1) (kind : Kind)
    (out mode gamma typ tag payload rest : OTerm alpha) : Formula alpha :=
  match kind with
  | .variable => StepVariable out gamma typ payload rest
  | .lambda => StepLambda out gamma typ payload rest
  | .application => StepApplication out gamma typ payload rest
  | .bottom => StepBottom out typ payload rest
  | .ordinary => StepOrdinary H out gamma typ payload rest
  | .numbered => StepNumbered H out gamma typ payload rest
  | .nil => StepArgumentsNil out typ payload rest
  | .cons => StepArgumentsCons out gamma typ payload rest
  | .terms => StepTermDispatch H out gamma typ tag payload rest
  | .arguments => StepArgumentsDispatch out gamma typ tag payload rest
  | .modes => StepModeDispatch H out mode gamma typ tag payload rest

theorem localSubst {beta : Type} (H : Program 1) (kind : Kind)
    (out mode gamma typ tag payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (LocalSpec H kind out mode gamma typ tag payload rest).subst (fun a => emb (ts a)) =
      LocalSpec H kind (out.subst ts) (mode.subst ts) (gamma.subst ts) (typ.subst ts)
        (tag.subst ts) (payload.subst ts) (rest.subst ts) := by
  cases kind <;> simp only [LocalSpec,stepVariableSubst,stepLambdaSubst,stepApplicationSubst,
    stepBottomSubst,stepOrdinarySubst,stepNumberedSubst,stepArgumentsNilSubst,stepArgumentsConsSubst,
    stepTermDispatchSubst,stepArgumentsDispatchSubst,stepModeDispatchSubst]

@[simp] theorem localRename {beta : Type} (H : Program 1) (kind : Kind)
    (out mode gamma typ tag payload rest : OTerm alpha) (j : alpha → beta) :
    (LocalSpec H kind out mode gamma typ tag payload rest).relabel j =
      LocalSpec H kind (out.relabel j) (mode.relabel j) (gamma.relabel j) (typ.relabel j)
        (tag.relabel j) (payload.relabel j) (rest.relabel j) := by
  cases kind <;> simp only [LocalSpec,stepVariableRename,stepLambdaRename,stepApplicationRename,
    stepBottomRename,stepOrdinaryRename,stepNumberedRename,stepArgumentsNilRename,stepArgumentsConsRename,
    stepTermDispatchRename,stepArgumentsDispatchRename,stepModeDispatchRename]

def localLiveFields (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix frontNext joinedNext nextState joinedNextState : OTerm alpha) : Formula alpha :=
  graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext suffix ⊓
    (StepLive nextState frontNext ⊓
      (StepLive joinedNextState joinedNext ⊓
        (LocalSpec H kind nextState mode gamma typ tag payload rest ⊓
          LocalSpec H kind joinedNextState mode gamma typ tag payload joinedRest)))

theorem localLiveFieldsSubst {beta : Type} (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix frontNext joinedNext nextState joinedNextState : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (localLiveFields H kind mode gamma typ tag payload rest joinedRest suffix frontNext joinedNext nextState joinedNextState).subst
      (fun a => emb (ts a)) = localLiveFields H kind (mode.subst ts) (gamma.subst ts) (typ.subst ts)
        (tag.subst ts) (payload.subst ts) (rest.subst ts) (joinedRest.subst ts) (suffix.subst ts)
        (frontNext.subst ts) (joinedNext.subst ts) (nextState.subst ts) (joinedNextState.subst ts) := by
  simp only [localLiveFields,conjunctionSubst,graph2Subst,stepLiveSubst,localSubst]

def localLiveMatrix (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  localLiveFields H kind (mode.relabel Sum.inl) (gamma.relabel Sum.inl) (typ.relabel Sum.inl)
    (tag.relabel Sum.inl) (payload.relabel Sum.inl) (rest.relabel Sum.inl)
    (joinedRest.relabel Sum.inl) (suffix.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

theorem localLiveWitness (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix frontNext joinedNext nextState joinedNextState : OTerm alpha) :
    (localLiveMatrix H kind mode gamma typ tag payload rest joinedRest suffix).subst
      (Sum.elim Term.var (fun i => emb (![frontNext,joinedNext,nextState,joinedNextState] i))) =
      localLiveFields H kind mode gamma typ tag payload rest joinedRest suffix frontNext joinedNext nextState joinedNextState := by
  unfold localLiveMatrix
  rw [witnessEmbedding,localLiveFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

/-- Paired independent original clauses, with constructed equal-suffix work.
Neither successful next-state compatibility nor transition outputs are premises. -/
def CoupledLocal (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix : OTerm alpha) : Formula alpha :=
  (LocalSpec H kind z mode gamma typ tag payload rest ⊓
    LocalSpec H kind z mode gamma typ tag payload joinedRest) ⊔
      InternalFiniteBlocks.block (localLiveMatrix H kind mode gamma typ tag payload rest joinedRest suffix)

theorem localCoupledSubst {beta : Type} (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix : OTerm alpha) (ts : alpha → OTerm beta) :
    (CoupledLocal H kind mode gamma typ tag payload rest joinedRest suffix).subst (fun a => emb (ts a)) =
      CoupledLocal H kind (mode.subst ts) (gamma.subst ts) (typ.subst ts) (tag.subst ts)
        (payload.subst ts) (rest.subst ts) (joinedRest.subst ts) (suffix.subst ts) := by
  change ((LocalSpec H kind z mode gamma typ tag payload rest ⊓
    LocalSpec H kind z mode gamma typ tag payload joinedRest).subst (fun a => emb (ts a))) ⊔
    ((InternalFiniteBlocks.block (localLiveMatrix H kind mode gamma typ tag payload rest joinedRest suffix)).subst
      (fun a => emb (ts a))) = _
  apply congrArg₂ (fun p q : Formula beta => p ⊔ q)
  · simp only [conjunctionSubst,localSubst,zSubst]
  · unfold InternalFiniteBlocks.block localLiveMatrix
    rw [exsSubst,bindSubst,liftedEmbedding]
    simp only [localLiveFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem localCoupledRename {beta : Type} (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix : OTerm alpha) (j : alpha → beta) :
    (CoupledLocal H kind mode gamma typ tag payload rest joinedRest suffix).relabel j =
      CoupledLocal H kind (mode.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j)
        (payload.relabel j) (rest.relabel j) (joinedRest.relabel j) (suffix.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (CoupledLocal H kind mode gamma typ tag payload rest joinedRest suffix).subst
    (fun a => emb (.var (j a))) = _
  rw [localCoupledSubst]
  simp only [← termRelabelAsSubst]

theorem localLiveIntro (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix frontNext joinedNext nextState joinedNextState : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext suffix)))
    (hf : Nonempty (Derivation body Delta (StepLive nextState frontNext)))
    (hj : Nonempty (Derivation body Delta (StepLive joinedNextState joinedNext)))
    (hs : Nonempty (Derivation body Delta (LocalSpec H kind nextState mode gamma typ tag payload rest)))
    (hjs : Nonempty (Derivation body Delta (LocalSpec H kind joinedNextState mode gamma typ tag payload joinedRest))) :
    Nonempty (Derivation body Delta (CoupledLocal H kind mode gamma typ tag payload rest joinedRest suffix)) := by
  have hb : Nonempty (Derivation body Delta
      (InternalFiniteBlocks.block (localLiveMatrix H kind mode gamma typ tag payload rest joinedRest suffix))) := by
    apply InternalFiniteBlocksProof.introduction body alpha 4 Delta
      (localLiveMatrix H kind mode gamma typ tag payload rest joinedRest suffix)
      (fun i => emb (![frontNext,joinedNext,nextState,joinedNextState] i))
    rw [localLiveWitness]
    exact andIntro ha (andIntro hf (andIntro hj (andIntro hs hjs)))
  obtain ⟨hb⟩ := hb
  exact ⟨InternalQuotientComparisonProof.orRight hb⟩

theorem localFailureIntro (H : Program 1) (kind : Kind)
    (mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (LocalSpec H kind z mode gamma typ tag payload rest)))
    (hjs : Nonempty (Derivation body Delta (LocalSpec H kind z mode gamma typ tag payload joinedRest))) :
    Nonempty (Derivation body Delta (CoupledLocal H kind mode gamma typ tag payload rest joinedRest suffix)) := by
  obtain ⟨h⟩ := andIntro hs hjs
  exact ⟨InternalQuotientComparisonProof.orLeft h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
