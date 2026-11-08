module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStepProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionInductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppend (append)
open InternalApplicationResultStackCompositionSyntaxProof
open InternalApplicationValidityStackAppendSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms
open InternalRawListRecursionSyntaxProof InternalNumericIterationSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Work, intermediate results, final results and suffix count are all inside
this full-language induction row; no standard-model count is substituted. -/
def workBody {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm α) : Formula (α ⊕ Fin 7) :=
  (graph2 append (.var (.inr 3)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    (actualRun guard leaf combine (count.relabel Sum.inl) (.var (.inr 1))
      (.var (.inr 4)) (.var (.inr 5)) ⊓
    actualRun guard leaf combine (.var (.inr 0)) (.var (.inr 2))
      (.var (.inr 5)) (.var (.inr 6)))).imp
    (actualRun guard leaf combine (OrdinaryArithmetic.addTerm (count.relabel Sum.inl) (.var (.inr 0)))
      (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 6)))

def workRow {α : Type} (guard leaf : Program 1) (combine : Program 4) (count : OTerm α) : Formula α :=
  allBlock (workBody guard leaf combine count)

/-- The result background is shared literally in both original append
premises. Original and framed initial/final stacks are universally bound. -/
def resultBody {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm α) : Formula (α ⊕ Fin 6) :=
  (actualRun guard leaf combine (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) ⊓
    (graph2 append (.var (.inr 4)) (.var (.inr 1)) (.var (.inr 3)) ⊓
      graph2 append (.var (.inr 5)) (.var (.inr 2)) (.var (.inr 3)))).imp
    (actualRun guard leaf combine (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 4)) (.var (.inr 5)))

def resultRow {α : Type} (guard leaf : Program 1) (combine : Program 4) (count : OTerm α) : Formula α :=
  allBlock (resultBody guard leaf combine count)

theorem workRowSubst {α β : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm α) (ts : α → OTerm β) :
    (workRow guard leaf combine count).subst (fun a => emb (ts a)) =
      workRow guard leaf combine (count.subst ts) := by
  unfold workRow workBody
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,graph2Subst,actualRunSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem workRowRename {α β : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm α) (j : α → β) :
    (workRow guard leaf combine count).relabel j = workRow guard leaf combine (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (workRow guard leaf combine count).subst (fun a => emb (.var (j a))) = _
  rw [workRowSubst]
  simp only [← termRelabelAsSubst]

theorem workBodyWitness {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count second frontWork suffix joined initialResults middleResults finalResults : OTerm α) :
    (workBody guard leaf combine count).subst
      (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined,initialResults,middleResults,finalResults] i))) =
      (graph2 append joined frontWork suffix ⊓
        (actualRun guard leaf combine count frontWork initialResults middleResults ⊓
          actualRun guard leaf combine second suffix middleResults finalResults)).imp
        (actualRun guard leaf combine (OrdinaryArithmetic.addTerm count second) joined initialResults finalResults) := by
  have he : (Sum.elim Term.var (fun i => emb (![second,frontWork,suffix,joined,initialResults,middleResults,finalResults] i))) =
      (fun a => emb (Sum.elim Term.var ![second,frontWork,suffix,joined,initialResults,middleResults,finalResults] a)) := by
    funext a
    cases a <;> rfl
  unfold workBody
  rw [he]
  simp only [impSubst,conjunctionSubst,graph2Subst,actualRunSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem workInstantiate {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (workRow guard leaf combine count) (emb t) =
      workRow guard leaf combine (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,workRowSubst]

theorem workSuccessor {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (workRow guard leaf combine count) =
      workRow guard leaf combine (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,workRowSubst]

theorem resultRowSubst {α β : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm α) (ts : α → OTerm β) :
    (resultRow guard leaf combine count).subst (fun a => emb (ts a)) =
      resultRow guard leaf combine (count.subst ts) := by
  unfold resultRow resultBody
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,graph2Subst,actualRunSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem resultRowRename {α β : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm α) (j : α → β) :
    (resultRow guard leaf combine count).relabel j = resultRow guard leaf combine (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (resultRow guard leaf combine count).subst (fun a => emb (.var (j a))) = _
  rw [resultRowSubst]
  simp only [← termRelabelAsSubst]

theorem resultBodyWitness {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults background framedInitial framedFinal : OTerm α) :
    (resultBody guard leaf combine count).subst
      (Sum.elim Term.var (fun i => emb (![work,initialResults,finalResults,background,framedInitial,framedFinal] i))) =
      (actualRun guard leaf combine count work initialResults finalResults ⊓
        (graph2 append framedInitial initialResults background ⊓
          graph2 append framedFinal finalResults background)).imp
        (actualRun guard leaf combine count work framedInitial framedFinal) := by
  have he : (Sum.elim Term.var (fun i => emb (![work,initialResults,finalResults,background,framedInitial,framedFinal] i))) =
      (fun a => emb (Sum.elim Term.var ![work,initialResults,finalResults,background,framedInitial,framedFinal] a)) := by
    funext a
    cases a <;> rfl
  unfold resultBody
  rw [he]
  simp only [impSubst,conjunctionSubst,graph2Subst,actualRunSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem resultInstantiate {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (resultRow guard leaf combine count) (emb t) =
      resultRow guard leaf combine (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,resultRowSubst]

theorem resultSuccessor {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (resultRow guard leaf combine count) =
      resultRow guard leaf combine (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,resultRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionInductionSyntaxProof
