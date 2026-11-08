module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionSyntaxProof
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

/-- All worklists and the suffix count stay inside the full-language induction
row, so the induction hypothesis applies to the actual successor worklist. -/
def appendBody {α : Type} (node leaf : Program 1) (count : OTerm α) : Formula (α ⊕ Fin 4) :=
  (graph2 append (.var (.inr 3)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    (successfulWork node leaf (count.relabel Sum.inl) (.var (.inr 1)) ⊓
      successfulWork node leaf (.var (.inr 0)) (.var (.inr 2)))).imp
    (successfulWork node leaf (OrdinaryArithmetic.addTerm (count.relabel Sum.inl) (.var (.inr 0)))
      (.var (.inr 3)))

def appendRow {α : Type} (node leaf : Program 1) (count : OTerm α) : Formula α :=
  allBlock (appendBody node leaf count)

theorem appendRowSubst {α β : Type} (node leaf : Program 1)
    (count : OTerm α) (ts : α → OTerm β) :
    (appendRow node leaf count).subst (fun a => emb (ts a)) =
      appendRow node leaf (count.subst ts) := by
  unfold appendRow appendBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,successfulWorkSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem appendRowRename {α β : Type} (node leaf : Program 1)
    (count : OTerm α) (j : α → β) :
    (appendRow node leaf count).relabel j = appendRow node leaf (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (appendRow node leaf count).subst (fun a => emb (.var (j a))) = _
  rw [appendRowSubst]
  simp only [← termRelabelAsSubst]

theorem appendBodyWitness {α : Type} (node leaf : Program 1)
    (count second frontWork suffix joined : OTerm α) :
    (appendBody node leaf count).subst
      (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined] i))) =
      (graph2 append joined frontWork suffix ⊓
        (successfulWork node leaf count frontWork ⊓ successfulWork node leaf second suffix)).imp
        (successfulWork node leaf (OrdinaryArithmetic.addTerm count second) joined) := by
  have he : (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined] i))) =
      (fun a => emb (Sum.elim Term.var ![second,frontWork,suffix,joined] a)) := by
    funext a
    cases a <;> rfl
  unfold appendBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,successfulWorkSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem appendInstantiate {α : Type} (node leaf : Program 1)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (appendRow node leaf count) (emb t) =
      appendRow node leaf (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,appendRowSubst]

theorem appendSuccessor {α : Type} (node leaf : Program 1) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (appendRow node leaf count) =
      appendRow node leaf (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,appendRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionSyntaxProof
