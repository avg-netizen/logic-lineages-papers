module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRunProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitSyntaxProof
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

open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalUniverseDecoderInternalFuelIterationProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalLambdaConstructorGraphSyntaxProof

/-- Both pieces are recovered at the same arbitrary symbolic run count. -/
def splitBody {α : Type} (H : Program 1) (M W : Program 2) (count : OTerm α) : Formula (α ⊕ Fin 4) :=
  (graph2 append (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1)) ⊓
    SuccessfulWork H M W (count.relabel Sum.inl) (.var (.inr 2)) (.var (.inr 3))).imp
    (SuccessfulWork H M W (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 3)) ⊓
      SuccessfulWork H M W (count.relabel Sum.inl) (.var (.inr 1)) (.var (.inr 3)))

def splitRow {α : Type} (H : Program 1) (M W : Program 2) (count : OTerm α) : Formula α :=
  allBlock (splitBody H M W count)

theorem splitRowSubst {α β : Type} (H : Program 1) (M W : Program 2)
    (count : OTerm α) (ts : α → OTerm β) :
    (splitRow H M W count).subst (fun a => emb (ts a)) =
      splitRow H M W (count.subst ts) := by
  unfold splitRow splitBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem splitRowRename {α β : Type} (H : Program 1) (M W : Program 2)
    (count : OTerm α) (j : α → β) :
    (splitRow H M W count).relabel j = splitRow H M W (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (splitRow H M W count).subst (fun a => emb (.var (j a))) = _
  rw [splitRowSubst]
  simp only [← termRelabelAsSubst]

theorem splitBodyWitness {α : Type} (H : Program 1) (M W : Program 2)
    (count frontWork suffix joined c : OTerm α) :
    (splitBody H M W count).subst
      (Sum.elim Term.var (fun i => emb (![frontWork,suffix,joined,c] i))) =
      (graph2 append joined frontWork suffix ⊓ SuccessfulWork H M W count joined c).imp
        (SuccessfulWork H M W count frontWork c ⊓ SuccessfulWork H M W count suffix c) := by
  have he : (Sum.elim Term.var (fun i => emb (![frontWork,suffix,joined,c] i))) =
      (fun a => emb (Sum.elim Term.var ![frontWork,suffix,joined,c] a)) := by
    funext a
    cases a <;> rfl
  unfold splitBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem splitInstantiate {α : Type} (H : Program 1) (M W : Program 2)
    (count : OTerm (α ⊕ Fin 1)) (x : OTerm α) :
    instantiate (splitRow H M W count) (emb x) =
      splitRow H M W (count.subst (bindTerm x)) := by
  rw [instantiate,bindEmbedding,splitRowSubst]

theorem splitSuccessor {α : Type} (H : Program 1) (M W : Program 2) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (splitRow H M W count) =
      splitRow H M W (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,splitRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitSyntaxProof
