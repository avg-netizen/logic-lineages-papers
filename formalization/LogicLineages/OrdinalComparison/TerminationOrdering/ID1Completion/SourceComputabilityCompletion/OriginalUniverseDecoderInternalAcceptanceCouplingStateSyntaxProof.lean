module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingStateSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingStateSyntaxProof
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

def liveFields {alpha : Type} (H : Program 1) (M W : Program 2)
    (state joinedState suffix c frontNext joinedNext nextState joinedNextState : OTerm alpha) : Formula alpha :=
  graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext suffix ⊓
    (StepLive nextState frontNext ⊓
      (StepLive joinedNextState joinedNext ⊓
        (graph2 (OriginalUniverseDecoder.transition H M W) nextState state c ⊓
          graph2 (OriginalUniverseDecoder.transition H M W) joinedNextState joinedState c)))

 theorem liveFieldsSubst {alpha beta : Type} (H : Program 1) (M W : Program 2)
    (state joinedState suffix c frontNext joinedNext nextState joinedNextState : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (liveFields H M W state joinedState suffix c frontNext joinedNext nextState joinedNextState).subst
      (fun a => emb (ts a)) = liveFields H M W (state.subst ts) (joinedState.subst ts)
        (suffix.subst ts) (c.subst ts) (frontNext.subst ts) (joinedNext.subst ts)
        (nextState.subst ts) (joinedNextState.subst ts) := by
  simp only [liveFields,conjunctionSubst,graph2Subst,stepLiveSubst]

def liveMatrix {alpha : Type} (H : Program 1) (M W : Program 2) (state joinedState suffix c : OTerm alpha) :
    Formula (alpha ⊕ Fin 4) :=
  liveFields H M W (state.relabel Sum.inl) (joinedState.relabel Sum.inl) (suffix.relabel Sum.inl) (c.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

 theorem liveMatrixWitness {alpha : Type} (H : Program 1) (M W : Program 2)
    (state joinedState suffix c frontNext joinedNext nextState joinedNextState : OTerm alpha) :
    (liveMatrix H M W state joinedState suffix c).subst
      (Sum.elim Term.var (fun i => emb (![frontNext,joinedNext,nextState,joinedNextState] i))) =
      liveFields H M W state joinedState suffix c frontNext joinedNext nextState joinedNextState := by
  unfold liveMatrix
  rw [witnessEmbedding,liveFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

/-- One-step coupling of the literal guarded source states. The same separate
outer context is retained by both transitions and every recursive witness. -/
def CoupledStep {alpha : Type} (H : Program 1) (M W : Program 2) (state joinedState suffix c : OTerm alpha) : Formula alpha :=
  (graph2 (OriginalUniverseDecoder.transition H M W) z state c ⊓ graph2 (OriginalUniverseDecoder.transition H M W) z joinedState c) ⊔
    InternalFiniteBlocks.block (liveMatrix H M W state joinedState suffix c)

 theorem coupledSubst {alpha beta : Type} (H : Program 1) (M W : Program 2) (state joinedState suffix c : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (CoupledStep H M W state joinedState suffix c).subst (fun a => emb (ts a)) =
      CoupledStep H M W (state.subst ts) (joinedState.subst ts) (suffix.subst ts) (c.subst ts) := by
  change ((graph2 (OriginalUniverseDecoder.transition H M W) z state c ⊓ graph2 (OriginalUniverseDecoder.transition H M W) z joinedState c).subst
    (fun a => emb (ts a))) ⊔ ((InternalFiniteBlocks.block (liveMatrix H M W state joinedState suffix c)).subst
      (fun a => emb (ts a))) = _
  apply congrArg₂ (fun p q : Formula beta => p ⊔ q)
  · simp only [conjunctionSubst,graph2Subst,zSubst]
  · unfold InternalFiniteBlocks.block liveMatrix
    rw [exsSubst,bindSubst,liftedEmbedding]
    simp only [liveFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem coupledRename {alpha beta : Type} (H : Program 1) (M W : Program 2)
    (state joinedState suffix c : OTerm alpha) (j : alpha → beta) :
    (CoupledStep H M W state joinedState suffix c).relabel j =
      CoupledStep H M W (state.relabel j) (joinedState.relabel j) (suffix.relabel j) (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (CoupledStep H M W state joinedState suffix c).subst (fun a => emb (.var (j a))) = _
  rw [coupledSubst]
  simp only [← termRelabelAsSubst]

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem coupledLiveIntro (H : Program 1) (M W : Program 2)
    (state joinedState suffix c frontNext joinedNext nextState joinedNextState : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (liveFields H M W state joinedState suffix c frontNext joinedNext nextState joinedNextState))) :
    Nonempty (Derivation body Delta (CoupledStep H M W state joinedState suffix c)) := by
  have hb : Nonempty (Derivation body Delta
      (InternalFiniteBlocks.block (liveMatrix H M W state joinedState suffix c))) := by
    apply InternalFiniteBlocksProof.introduction body alpha 4 Delta (liveMatrix H M W state joinedState suffix c)
      (fun i => emb (![frontNext,joinedNext,nextState,joinedNextState] i))
    rw [liveMatrixWitness]
    exact h
  obtain ⟨hb⟩ := hb
  exact ⟨InternalQuotientComparisonProof.orRight hb⟩

 theorem coupledFailureIntro (H : Program 1) (M W : Program 2) (state joinedState suffix c : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.transition H M W) z state c)))
    (hjf : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.transition H M W) z joinedState c))) :
    Nonempty (Derivation body Delta (CoupledStep H M W state joinedState suffix c)) := by
  obtain ⟨h⟩ := andIntro hf hjf
  exact ⟨InternalQuotientComparisonProof.orLeft h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingStateSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceCouplingStateSyntaxProof
