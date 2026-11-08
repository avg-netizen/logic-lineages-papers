module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationResultStackComposition InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationValidityStackAppendSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms
open InternalRawListRecursionSyntaxProof InternalNumericIterationSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-only name for the inner existential block of the frozen Run. -/
def runEnd {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count state finalResults : OTerm α) : Formula α :=
  existsOne
    (graph1 InternalApplicationResultStack.emptyState (.var (.inr (0 : Fin 1)))
        (finalResults.relabel Sum.inl) ⊓
      graph2 (InternalApplicationResultStack.iterate guard leaf combine)
        (.var (.inr (0 : Fin 1))) (count.relabel Sum.inl) (state.relabel Sum.inl))

@[simp] theorem graph1Subst {α β : Type} (p : Program 1)
    (out x : OTerm α) (ts : α → OTerm β) :
    (graph1 p out x).subst (fun a => emb (ts a)) =
      graph1 p (out.subst ts) (x.subst ts) := by
  simp only [graph1,programSubst,consTermSubst,emptySubst]

theorem runEndSubst {α β : Type} (guard leaf : Program 1) (combine : Program 4)
    (count state finalResults : OTerm α) (ts : α → OTerm β) :
    (runEnd guard leaf combine count state finalResults).subst (fun a => emb (ts a)) =
      runEnd guard leaf combine (count.subst ts) (state.subst ts) (finalResults.subst ts) := by
  unfold runEnd
  rw [existsSubst,liftedEmbedding,conjunctionSubst]
  simp only [graph1Subst,graph2Subst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem runEndRename {α β : Type} (guard leaf : Program 1) (combine : Program 4)
    (count state finalResults : OTerm α) (j : α → β) :
    (runEnd guard leaf combine count state finalResults).relabel j =
      runEnd guard leaf combine (count.relabel j) (state.relabel j) (finalResults.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (runEnd guard leaf combine count state finalResults).subst (fun a => emb (.var (j a))) = _
  rw [runEndSubst]
  simp only [← termRelabelAsSubst]

theorem actualRunSubst {α β : Type} (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults : OTerm α) (ts : α → OTerm β) :
    (actualRun guard leaf combine count work initialResults finalResults).subst (fun a => emb (ts a)) =
      actualRun guard leaf combine (count.subst ts) (work.subst ts)
        (initialResults.subst ts) (finalResults.subst ts) := by
  change (existsOne (graph2 liveState (.var (.inr (0 : Fin 1)))
    (work.relabel Sum.inl) (initialResults.relabel Sum.inl) ⊓
    runEnd guard leaf combine (count.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
      (finalResults.relabel Sum.inl))).subst (fun a => emb (ts a)) = _
  rw [existsSubst,liftedEmbedding,conjunctionSubst]
  simp only [graph2Subst,runEndSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem actualRunRename {α β : Type} (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults : OTerm α) (j : α → β) :
    (actualRun guard leaf combine count work initialResults finalResults).relabel j =
      actualRun guard leaf combine (count.relabel j) (work.relabel j)
        (initialResults.relabel j) (finalResults.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (actualRun guard leaf combine count work initialResults finalResults).subst
    (fun a => emb (.var (j a))) = _
  rw [actualRunSubst]
  simp only [← termRelabelAsSubst]

theorem runEndInstance {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count state finalResults finalState : OTerm α) :
    instantiate (graph1 InternalApplicationResultStack.emptyState (.var (.inr (0 : Fin 1)))
        (finalResults.relabel Sum.inl) ⊓
      graph2 (InternalApplicationResultStack.iterate guard leaf combine)
        (.var (.inr (0 : Fin 1))) (count.relabel Sum.inl) (state.relabel Sum.inl)) (emb finalState) =
      graph1 InternalApplicationResultStack.emptyState finalState finalResults ⊓
        graph2 (InternalApplicationResultStack.iterate guard leaf combine) finalState count state := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [graph1Subst,graph2Subst,liftBind,varBind]

theorem actualRunInstance {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (count work initialResults finalResults state : OTerm α) :
    instantiate (graph2 liveState (.var (.inr (0 : Fin 1)))
        (work.relabel Sum.inl) (initialResults.relabel Sum.inl) ⊓
      runEnd guard leaf combine (count.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
        (finalResults.relabel Sum.inl)) (emb state) =
      graph2 liveState state work initialResults ⊓ runEnd guard leaf combine count state finalResults := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [graph2Subst,runEndSubst,liftBind,varBind]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionSyntaxProof
