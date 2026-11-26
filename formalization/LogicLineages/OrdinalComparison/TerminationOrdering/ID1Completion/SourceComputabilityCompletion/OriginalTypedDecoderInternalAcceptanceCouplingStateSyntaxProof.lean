module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingStateSyntaxProof
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

 theorem unarySubst {alpha beta : Type} (p : Program 1) (out input : OTerm alpha) (ts : alpha → OTerm beta) :
    (graph1 p out input).subst (fun a => emb (ts a)) = graph1 p (out.subst ts) (input.subst ts) := by
  simp only [graph1,programSubst,consTermSubst,emptySubst]

def liveFields {alpha : Type} (H : Program 1)
    (state joinedState suffix frontNext joinedNext nextState joinedNextState : OTerm alpha) : Formula alpha :=
  graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext suffix ⊓
    (StepLive nextState frontNext ⊓
      (StepLive joinedNextState joinedNext ⊓
        (graph1 (OriginalTypedDecoder.transition H) nextState state ⊓
          graph1 (OriginalTypedDecoder.transition H) joinedNextState joinedState)))

 theorem liveFieldsSubst {alpha beta : Type} (H : Program 1)
    (state joinedState suffix frontNext joinedNext nextState joinedNextState : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (liveFields H state joinedState suffix frontNext joinedNext nextState joinedNextState).subst
      (fun a => emb (ts a)) = liveFields H (state.subst ts) (joinedState.subst ts)
        (suffix.subst ts) (frontNext.subst ts) (joinedNext.subst ts)
        (nextState.subst ts) (joinedNextState.subst ts) := by
  simp only [liveFields,conjunctionSubst,graph2Subst,stepLiveSubst,unarySubst]

def liveMatrix {alpha : Type} (H : Program 1) (state joinedState suffix : OTerm alpha) :
    Formula (alpha ⊕ Fin 4) :=
  liveFields H (state.relabel Sum.inl) (joinedState.relabel Sum.inl) (suffix.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

 theorem liveMatrixWitness {alpha : Type} (H : Program 1)
    (state joinedState suffix frontNext joinedNext nextState joinedNextState : OTerm alpha) :
    (liveMatrix H state joinedState suffix).subst
      (Sum.elim Term.var (fun i => emb (![frontNext,joinedNext,nextState,joinedNextState] i))) =
      liveFields H state joinedState suffix frontNext joinedNext nextState joinedNextState := by
  unfold liveMatrix
  rw [witnessEmbedding,liveFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

/-- One-step coupling of actual states through actual raw append. -/
def CoupledStep {alpha : Type} (H : Program 1) (state joinedState suffix : OTerm alpha) : Formula alpha :=
  (graph1 (OriginalTypedDecoder.transition H) z state ⊓ graph1 (OriginalTypedDecoder.transition H) z joinedState) ⊔
    InternalFiniteBlocks.block (liveMatrix H state joinedState suffix)

 theorem coupledSubst {alpha beta : Type} (H : Program 1) (state joinedState suffix : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (CoupledStep H state joinedState suffix).subst (fun a => emb (ts a)) =
      CoupledStep H (state.subst ts) (joinedState.subst ts) (suffix.subst ts) := by
  change ((graph1 (OriginalTypedDecoder.transition H) z state ⊓ graph1 (OriginalTypedDecoder.transition H) z joinedState).subst
    (fun a => emb (ts a))) ⊔ ((InternalFiniteBlocks.block (liveMatrix H state joinedState suffix)).subst
      (fun a => emb (ts a))) = _
  apply congrArg₂ (fun p q : Formula beta => p ⊔ q)
  · simp only [conjunctionSubst,unarySubst,zSubst]
  · unfold InternalFiniteBlocks.block liveMatrix
    rw [exsSubst,bindSubst,liftedEmbedding]
    simp only [liveFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem coupledRename {alpha beta : Type} (H : Program 1)
    (state joinedState suffix : OTerm alpha) (j : alpha → beta) :
    (CoupledStep H state joinedState suffix).relabel j =
      CoupledStep H (state.relabel j) (joinedState.relabel j) (suffix.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (CoupledStep H state joinedState suffix).subst (fun a => emb (.var (j a))) = _
  rw [coupledSubst]
  simp only [← termRelabelAsSubst]

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem coupledLiveIntro (H : Program 1)
    (state joinedState suffix frontNext joinedNext nextState joinedNextState : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (liveFields H state joinedState suffix frontNext joinedNext nextState joinedNextState))) :
    Nonempty (Derivation body Delta (CoupledStep H state joinedState suffix)) := by
  have hb : Nonempty (Derivation body Delta
      (InternalFiniteBlocks.block (liveMatrix H state joinedState suffix))) := by
    apply InternalFiniteBlocksProof.introduction body alpha 4 Delta (liveMatrix H state joinedState suffix)
      (fun i => emb (![frontNext,joinedNext,nextState,joinedNextState] i))
    rw [liveMatrixWitness]
    exact h
  obtain ⟨hb⟩ := hb
  exact ⟨InternalQuotientComparisonProof.orRight hb⟩

 theorem coupledFailureIntro (H : Program 1) (state joinedState suffix : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalTypedDecoder.transition H) z state)))
    (hjf : Nonempty (Derivation body Delta (graph1 (OriginalTypedDecoder.transition H) z joinedState))) :
    Nonempty (Derivation body Delta (CoupledStep H state joinedState suffix)) := by
  obtain ⟨h⟩ := andIntro hf hjf
  exact ⟨InternalQuotientComparisonProof.orLeft h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingStateSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingStateSyntaxProof
