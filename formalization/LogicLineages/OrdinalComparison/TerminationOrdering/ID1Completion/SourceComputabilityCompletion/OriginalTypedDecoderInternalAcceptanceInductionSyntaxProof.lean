module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRunProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSyntaxProof
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

open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

/-- All worklists and the suffix count stay inside the full-language induction
row, so the induction hypothesis applies to the actual successor worklist. -/
def appendBody {α : Type} (H : Program 1) (count : OTerm α) : Formula (α ⊕ Fin 4) :=
  (graph2 append (.var (.inr 3)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    (SuccessfulWork H (count.relabel Sum.inl) (.var (.inr 1)) ⊓
      SuccessfulWork H (.var (.inr 0)) (.var (.inr 2)))).imp
    (SuccessfulWork H (OrdinaryArithmetic.addTerm (count.relabel Sum.inl) (.var (.inr 0)))
      (.var (.inr 3)))

def appendRow {α : Type} (H : Program 1) (count : OTerm α) : Formula α :=
  allBlock (appendBody H count)

theorem appendRowSubst {α β : Type} (H : Program 1)
    (count : OTerm α) (ts : α → OTerm β) :
    (appendRow H count).subst (fun a => emb (ts a)) =
      appendRow H (count.subst ts) := by
  unfold appendRow appendBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem appendRowRename {α β : Type} (H : Program 1)
    (count : OTerm α) (j : α → β) :
    (appendRow H count).relabel j = appendRow H (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (appendRow H count).subst (fun a => emb (.var (j a))) = _
  rw [appendRowSubst]
  simp only [← termRelabelAsSubst]

theorem appendBodyWitness {α : Type} (H : Program 1)
    (count second frontWork suffix joined : OTerm α) :
    (appendBody H count).subst
      (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined] i))) =
      (graph2 append joined frontWork suffix ⊓
        (SuccessfulWork H count frontWork ⊓ SuccessfulWork H second suffix)).imp
        (SuccessfulWork H (OrdinaryArithmetic.addTerm count second) joined) := by
  have he : (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined] i))) =
      (fun a => emb (Sum.elim Term.var ![second,frontWork,suffix,joined] a)) := by
    funext a
    cases a <;> rfl
  unfold appendBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem appendInstantiate {α : Type} (H : Program 1)
    (count : OTerm (α ⊕ Fin 1)) (x : OTerm α) :
    instantiate (appendRow H count) (emb x) =
      appendRow H (count.subst (bindTerm x)) := by
  rw [instantiate,bindEmbedding,appendRowSubst]

theorem appendSuccessor {α : Type} (H : Program 1) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (appendRow H count) =
      appendRow H (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,appendRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSyntaxProof
