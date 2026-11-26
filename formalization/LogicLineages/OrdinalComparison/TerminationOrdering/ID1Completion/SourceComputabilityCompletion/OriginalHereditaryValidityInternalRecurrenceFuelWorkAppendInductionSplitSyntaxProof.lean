module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendRunProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms
open InternalRawListRecursionSyntaxProof InternalNumericIterationSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

/-- Both pieces are recovered at the same arbitrary symbolic run count. -/
def splitBody {α : Type} (s t m : Program 2) (count : OTerm α) : Formula (α ⊕ Fin 3) :=
  (graph2 append (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1)) ⊓
    SuccessfulWork s t m (count.relabel Sum.inl) (.var (.inr 2))).imp
    (SuccessfulWork s t m (count.relabel Sum.inl) (.var (.inr 0)) ⊓
      SuccessfulWork s t m (count.relabel Sum.inl) (.var (.inr 1)))

def splitRow {α : Type} (s t m : Program 2) (count : OTerm α) : Formula α :=
  allBlock (splitBody s t m count)

theorem splitRowSubst {α β : Type} (s t m : Program 2)
    (count : OTerm α) (ts : α → OTerm β) :
    (splitRow s t m count).subst (fun a => emb (ts a)) =
      splitRow s t m (count.subst ts) := by
  unfold splitRow splitBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof.successfulWorkSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem splitRowRename {α β : Type} (s t m : Program 2)
    (count : OTerm α) (j : α → β) :
    (splitRow s t m count).relabel j = splitRow s t m (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (splitRow s t m count).subst (fun a => emb (.var (j a))) = _
  rw [splitRowSubst]
  simp only [← termRelabelAsSubst]

theorem splitBodyWitness {α : Type} (s t m : Program 2)
    (count frontWork suffix joined : OTerm α) :
    (splitBody s t m count).subst
      (Sum.elim Term.var (fun i => emb (![frontWork,suffix,joined] i))) =
      (graph2 append joined frontWork suffix ⊓ SuccessfulWork s t m count joined).imp
        (SuccessfulWork s t m count frontWork ⊓ SuccessfulWork s t m count suffix) := by
  have he : (Sum.elim Term.var (fun i => emb (![frontWork,suffix,joined] i))) =
      (fun a => emb (Sum.elim Term.var ![frontWork,suffix,joined] a)) := by
    funext a
    cases a <;> rfl
  unfold splitBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof.successfulWorkSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem splitInstantiate {α : Type} (s t m : Program 2)
    (count : OTerm (α ⊕ Fin 1)) (x : OTerm α) :
    instantiate (splitRow s t m count) (emb x) =
      splitRow s t m (count.subst (bindTerm x)) := by
  rw [instantiate,bindEmbedding,splitRowSubst]

theorem splitSuccessor {α : Type} (s t m : Program 2) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (splitRow s t m count) =
      splitRow s t m (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,splitRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSplitSyntaxProof
