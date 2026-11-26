module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelZeroSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendSyntaxProof InternalRawListRecursionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalPushSyntaxProof OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelAppendSyntaxProof

def decreasedFields {alpha : Type} (out previous work count : OTerm alpha) : Formula alpha :=
  StateGraph out (numeral 1) work ⊓
    (WorkFuelGraph count work ⊓ InternalLessThan.strictLess count previous)

 theorem decreasedFieldsSubst {alpha beta : Type} (out previous work count : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (decreasedFields out previous work count).subst (fun a => emb (ts a)) =
      decreasedFields (out.subst ts) (previous.subst ts) (work.subst ts) (count.subst ts) := by
  simp only [decreasedFields,StateGraph,conjunctionSubst,graph2Subst,fuelSubst,
    InternalLessThan.strictLess,orderSubst,numeral,sucSubst,zSubst]

/-- The right disjunct is the original live state with an internally computed
strictly smaller pending payload sum. -/
def decreasedBody {alpha : Type} (out previous : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  decreasedFields (out.relabel Sum.inl) (previous.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))

 theorem decreasedBodyWitness {alpha : Type} (out previous work count : OTerm alpha) :
    (decreasedBody out previous).subst
      (Sum.elim Term.var (fun i => emb (![work,count] i))) =
      StateGraph out (numeral 1) work ⊓
        (WorkFuelGraph count work ⊓ InternalLessThan.strictLess count previous) := by
  unfold decreasedBody
  rw [witnessEmbedding,decreasedFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

 theorem decreasedSubst {alpha beta : Type} (out previous : OTerm alpha) (ts : alpha → OTerm beta) :
    (DecreasedOrFailed out previous).subst (fun a => emb (ts a)) =
      DecreasedOrFailed (out.subst ts) (previous.subst ts) := by
  change ((equal out z).subst (fun a => emb (ts a))) ⊔
    ((InternalFiniteBlocks.block (decreasedBody out previous)).subst (fun a => emb (ts a))) =
      equal (out.subst ts) z ⊔
        InternalFiniteBlocks.block (decreasedBody (out.subst ts) (previous.subst ts))
  apply congrArg₂ (fun p q : Formula beta => p ⊔ q)
  · simp only [equalEqn,eqnSubst,zSubst]
  · unfold InternalFiniteBlocks.block decreasedBody
    rw [exsSubst,bindSubst,liftedEmbedding]
    simp only [decreasedFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem decreasedRename {alpha beta : Type} (out previous : OTerm alpha) (j : alpha → beta) :
    (DecreasedOrFailed out previous).relabel j =
      DecreasedOrFailed (out.relabel j) (previous.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (DecreasedOrFailed out previous).subst (fun a => emb (.var (j a))) = _
  rw [decreasedSubst]
  simp only [← termRelabelAsSubst]

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem decreasedIntro (out previous work count : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateGraph out (numeral 1) work)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph count work)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess count previous))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  have h : Nonempty (Derivation body Delta (InternalFiniteBlocks.block (decreasedBody out previous))) := by
    apply InternalFiniteBlocksProof.introduction body alpha 2 Delta (decreasedBody out previous)
      (fun i => emb (![work,count] i))
    rw [decreasedBodyWitness]
    exact andIntro hs (andIntro hf hl)
  obtain ⟨h⟩ := h
  exact ⟨InternalQuotientComparisonProof.orRight h⟩

 theorem failedIntro (out previous : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (equal out z))) :
    Nonempty (Derivation body Delta (DecreasedOrFailed out previous)) := by
  obtain ⟨hz⟩ := hz
  exact ⟨InternalQuotientComparisonProof.orLeft hz⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseSyntaxProof
