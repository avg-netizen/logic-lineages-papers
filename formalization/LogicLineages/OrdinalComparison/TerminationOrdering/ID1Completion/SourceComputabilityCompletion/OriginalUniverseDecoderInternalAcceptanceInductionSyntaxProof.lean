module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRunProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSyntaxProof
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

/-- All worklists and the suffix count stay inside the full-language induction
row, so the induction hypothesis applies to the actual successor worklist. -/
def appendBody {α : Type} (H : Program 1) (M W : Program 2) (count : OTerm α) : Formula (α ⊕ Fin 5) :=
  (graph2 append (.var (.inr 3)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    (SuccessfulWork H M W (count.relabel Sum.inl) (.var (.inr 1)) (.var (.inr 4)) ⊓
      SuccessfulWork H M W (.var (.inr 0)) (.var (.inr 2)) (.var (.inr 4)))).imp
    (SuccessfulWork H M W (OrdinaryArithmetic.addTerm (count.relabel Sum.inl) (.var (.inr 0)))
      (.var (.inr 3)) (.var (.inr 4)))

def appendRow {α : Type} (H : Program 1) (M W : Program 2) (count : OTerm α) : Formula α :=
  allBlock (appendBody H M W count)

theorem appendRowSubst {α β : Type} (H : Program 1) (M W : Program 2)
    (count : OTerm α) (ts : α → OTerm β) :
    (appendRow H M W count).subst (fun a => emb (ts a)) =
      appendRow H M W (count.subst ts) := by
  unfold appendRow appendBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem appendRowRename {α β : Type} (H : Program 1) (M W : Program 2)
    (count : OTerm α) (j : α → β) :
    (appendRow H M W count).relabel j = appendRow H M W (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (appendRow H M W count).subst (fun a => emb (.var (j a))) = _
  rw [appendRowSubst]
  simp only [← termRelabelAsSubst]

theorem appendBodyWitness {α : Type} (H : Program 1) (M W : Program 2)
    (count second frontWork suffix joined c : OTerm α) :
    (appendBody H M W count).subst
      (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined,c] i))) =
      (graph2 append joined frontWork suffix ⊓
        (SuccessfulWork H M W count frontWork c ⊓ SuccessfulWork H M W second suffix c)).imp
        (SuccessfulWork H M W (OrdinaryArithmetic.addTerm count second) joined c) := by
  have he : (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined,c] i))) =
      (fun a => emb (Sum.elim Term.var ![second,frontWork,suffix,joined,c] a)) := by
    funext a
    cases a <;> rfl
  unfold appendBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,OriginalUniverseDecoderInternalFuelIterationSyntaxProof.successfulWorkSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem appendInstantiate {α : Type} (H : Program 1) (M W : Program 2)
    (count : OTerm (α ⊕ Fin 1)) (x : OTerm α) :
    instantiate (appendRow H M W count) (emb x) =
      appendRow H M W (count.subst (bindTerm x)) := by
  rw [instantiate,bindEmbedding,appendRowSubst]

theorem appendSuccessor {α : Type} (H : Program 1) (M W : Program 2) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (appendRow H M W count) =
      appendRow H M W (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,appendRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSyntaxProof
