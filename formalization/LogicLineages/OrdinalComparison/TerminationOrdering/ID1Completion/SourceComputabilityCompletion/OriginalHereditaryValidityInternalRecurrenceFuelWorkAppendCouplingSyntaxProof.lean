module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendSyntaxProof InternalRawListRecursionSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof OriginalHereditaryValidityInternalPushSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem unarySubst {alpha beta : Type} (p : Program 1) (out input : OTerm alpha) (ts : alpha → OTerm beta) :
    (graph1 p out input).subst (fun a => emb (ts a)) = graph1 p (out.subst ts) (input.subst ts) := by
  simp only [graph1,programSubst,consTermSubst,emptySubst]

def liveFields {alpha : Type} (s t m : Program 2)
    (state joinedState suffix frontNext joinedNext nextState joinedNextState : OTerm alpha) : Formula alpha :=
  graph2 InternalApplicationValidityStackAppend.append joinedNext frontNext suffix ⊓
    (StateGraph nextState (numeral 1) frontNext ⊓
      (StateGraph joinedNextState (numeral 1) joinedNext ⊓
        (graph1 (transition s t m) nextState state ⊓
          graph1 (transition s t m) joinedNextState joinedState)))

 theorem liveFieldsSubst {alpha beta : Type} (s t m : Program 2)
    (state joinedState suffix frontNext joinedNext nextState joinedNextState : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (liveFields s t m state joinedState suffix frontNext joinedNext nextState joinedNextState).subst
      (fun a => emb (ts a)) = liveFields s t m (state.subst ts) (joinedState.subst ts)
        (suffix.subst ts) (frontNext.subst ts) (joinedNext.subst ts)
        (nextState.subst ts) (joinedNextState.subst ts) := by
  simp only [liveFields,StateGraph,conjunctionSubst,graph2Subst,unarySubst,numeral,sucSubst,zSubst]

def liveMatrix {alpha : Type} (s t m : Program 2) (state joinedState suffix : OTerm alpha) :
    Formula (alpha ⊕ Fin 4) :=
  liveFields s t m (state.relabel Sum.inl) (joinedState.relabel Sum.inl) (suffix.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

 theorem liveMatrixWitness {alpha : Type} (s t m : Program 2)
    (state joinedState suffix frontNext joinedNext nextState joinedNextState : OTerm alpha) :
    (liveMatrix s t m state joinedState suffix).subst
      (Sum.elim Term.var (fun i => emb (![frontNext,joinedNext,nextState,joinedNextState] i))) =
      liveFields s t m state joinedState suffix frontNext joinedNext nextState joinedNextState := by
  unfold liveMatrix
  rw [witnessEmbedding,liveFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

/-- One-step coupling of actual states through actual raw append. -/
def CoupledStep {alpha : Type} (s t m : Program 2) (state joinedState suffix : OTerm alpha) : Formula alpha :=
  (graph1 (transition s t m) z state ⊓ graph1 (transition s t m) z joinedState) ⊔
    InternalFiniteBlocks.block (liveMatrix s t m state joinedState suffix)

 theorem coupledSubst {alpha beta : Type} (s t m : Program 2) (state joinedState suffix : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (CoupledStep s t m state joinedState suffix).subst (fun a => emb (ts a)) =
      CoupledStep s t m (state.subst ts) (joinedState.subst ts) (suffix.subst ts) := by
  change ((graph1 (transition s t m) z state ⊓ graph1 (transition s t m) z joinedState).subst
    (fun a => emb (ts a))) ⊔ ((InternalFiniteBlocks.block (liveMatrix s t m state joinedState suffix)).subst
      (fun a => emb (ts a))) = _
  apply congrArg₂ (fun p q : Formula beta => p ⊔ q)
  · simp only [conjunctionSubst,unarySubst,zSubst]
  · unfold InternalFiniteBlocks.block liveMatrix
    rw [exsSubst,bindSubst,liftedEmbedding]
    simp only [liveFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem coupledRename {alpha beta : Type} (s t m : Program 2)
    (state joinedState suffix : OTerm alpha) (j : alpha → beta) :
    (CoupledStep s t m state joinedState suffix).relabel j =
      CoupledStep s t m (state.relabel j) (joinedState.relabel j) (suffix.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (CoupledStep s t m state joinedState suffix).subst (fun a => emb (.var (j a))) = _
  rw [coupledSubst]
  simp only [← termRelabelAsSubst]

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem coupledLiveIntro (s t m : Program 2)
    (state joinedState suffix frontNext joinedNext nextState joinedNextState : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (liveFields s t m state joinedState suffix frontNext joinedNext nextState joinedNextState))) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  have hb : Nonempty (Derivation body Delta
      (InternalFiniteBlocks.block (liveMatrix s t m state joinedState suffix))) := by
    apply InternalFiniteBlocksProof.introduction body alpha 4 Delta (liveMatrix s t m state joinedState suffix)
      (fun i => emb (![frontNext,joinedNext,nextState,joinedNextState] i))
    rw [liveMatrixWitness]
    exact h
  obtain ⟨hb⟩ := hb
  exact ⟨InternalQuotientComparisonProof.orRight hb⟩

 theorem coupledFailureIntro (s t m : Program 2) (state joinedState suffix : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 (transition s t m) z state)))
    (hjf : Nonempty (Derivation body Delta (graph1 (transition s t m) z joinedState))) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  obtain ⟨h⟩ := andIntro hf hjf
  exact ⟨InternalQuotientComparisonProof.orLeft h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
