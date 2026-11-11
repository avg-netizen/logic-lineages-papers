module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendRunProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSyntaxProof
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

/-- All worklists and the suffix count stay inside the full-language induction
row, so the induction hypothesis applies to the actual successor worklist. -/
def appendBody {α : Type} (s t m : Program 2) (count : OTerm α) : Formula (α ⊕ Fin 4) :=
  (graph2 append (.var (.inr 3)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    (SuccessfulWork s t m (count.relabel Sum.inl) (.var (.inr 1)) ⊓
      SuccessfulWork s t m (.var (.inr 0)) (.var (.inr 2)))).imp
    (SuccessfulWork s t m (OrdinaryArithmetic.addTerm (count.relabel Sum.inl) (.var (.inr 0)))
      (.var (.inr 3)))

def appendRow {α : Type} (s t m : Program 2) (count : OTerm α) : Formula α :=
  allBlock (appendBody s t m count)

theorem appendRowSubst {α β : Type} (s t m : Program 2)
    (count : OTerm α) (ts : α → OTerm β) :
    (appendRow s t m count).subst (fun a => emb (ts a)) =
      appendRow s t m (count.subst ts) := by
  unfold appendRow appendBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof.successfulWorkSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem appendRowRename {α β : Type} (s t m : Program 2)
    (count : OTerm α) (j : α → β) :
    (appendRow s t m count).relabel j = appendRow s t m (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (appendRow s t m count).subst (fun a => emb (.var (j a))) = _
  rw [appendRowSubst]
  simp only [← termRelabelAsSubst]

theorem appendBodyWitness {α : Type} (s t m : Program 2)
    (count second frontWork suffix joined : OTerm α) :
    (appendBody s t m count).subst
      (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined] i))) =
      (graph2 append joined frontWork suffix ⊓
        (SuccessfulWork s t m count frontWork ⊓ SuccessfulWork s t m second suffix)).imp
        (SuccessfulWork s t m (OrdinaryArithmetic.addTerm count second) joined) := by
  have he : (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined] i))) =
      (fun a => emb (Sum.elim Term.var ![second,frontWork,suffix,joined] a)) := by
    funext a
    cases a <;> rfl
  unfold appendBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof.successfulWorkSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem appendInstantiate {α : Type} (s t m : Program 2)
    (count : OTerm (α ⊕ Fin 1)) (x : OTerm α) :
    instantiate (appendRow s t m count) (emb x) =
      appendRow s t m (count.subst (bindTerm x)) := by
  rw [instantiate,bindEmbedding,appendRowSubst]

theorem appendSuccessor {α : Type} (s t m : Program 2) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (appendRow s t m count) =
      appendRow s t m (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,appendRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendInductionSyntaxProof
