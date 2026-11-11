module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRunProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSplitSyntaxProof
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

/-- Both pieces are recovered at the same arbitrary symbolic run count. -/
def splitBody {α : Type} (H : Program 1) (count : OTerm α) : Formula (α ⊕ Fin 3) :=
  (graph2 append (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1)) ⊓
    SuccessfulWork H (count.relabel Sum.inl) (.var (.inr 2))).imp
    (SuccessfulWork H (count.relabel Sum.inl) (.var (.inr 0)) ⊓
      SuccessfulWork H (count.relabel Sum.inl) (.var (.inr 1)))

def splitRow {α : Type} (H : Program 1) (count : OTerm α) : Formula α :=
  allBlock (splitBody H count)

theorem splitRowSubst {α β : Type} (H : Program 1)
    (count : OTerm α) (ts : α → OTerm β) :
    (splitRow H count).subst (fun a => emb (ts a)) =
      splitRow H (count.subst ts) := by
  unfold splitRow splitBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem splitRowRename {α β : Type} (H : Program 1)
    (count : OTerm α) (j : α → β) :
    (splitRow H count).relabel j = splitRow H (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (splitRow H count).subst (fun a => emb (.var (j a))) = _
  rw [splitRowSubst]
  simp only [← termRelabelAsSubst]

theorem splitBodyWitness {α : Type} (H : Program 1)
    (count frontWork suffix joined : OTerm α) :
    (splitBody H count).subst
      (Sum.elim Term.var (fun i => emb (![frontWork,suffix,joined] i))) =
      (graph2 append joined frontWork suffix ⊓ SuccessfulWork H count joined).imp
        (SuccessfulWork H count frontWork ⊓ SuccessfulWork H count suffix) := by
  have he : (Sum.elim Term.var (fun i => emb (![frontWork,suffix,joined] i))) =
      (fun a => emb (Sum.elim Term.var ![frontWork,suffix,joined] a)) := by
    funext a
    cases a <;> rfl
  unfold splitBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalTypedDecoderInternalFuelIterationSyntaxProof.successfulWorkSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem splitInstantiate {α : Type} (H : Program 1)
    (count : OTerm (α ⊕ Fin 1)) (x : OTerm α) :
    instantiate (splitRow H count) (emb x) =
      splitRow H (count.subst (bindTerm x)) := by
  rw [instantiate,bindEmbedding,splitRowSubst]

theorem splitSuccessor {α : Type} (H : Program 1) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (splitRow H count) =
      splitRow H (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,splitRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSplitSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSplitSyntaxProof
