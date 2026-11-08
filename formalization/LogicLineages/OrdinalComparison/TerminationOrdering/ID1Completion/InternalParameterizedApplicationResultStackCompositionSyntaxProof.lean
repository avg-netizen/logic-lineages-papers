module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionTargets
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionSyntaxProof
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

/-- Proof-only argument order for the unchanged frozen successful-run formula. -/
abbrev run {α : Type} (guard leaf : Program 2) (combine : Program 5)
    (parameter count work initialResults finalResults : OTerm α) : Formula α :=
  InternalParameterizedApplicationResultStackComposition.actualRunP guard leaf combine
    count work initialResults finalResults parameter

@[simp] theorem graph3Subst {α β : Type} (p : Program 3)
    (out x y z : OTerm α) (ts : α → OTerm β) :
    (graph3 p out x y z).subst (fun a => emb (ts a)) =
      graph3 p (out.subst ts) (x.subst ts) (y.subst ts) (z.subst ts) := by
  simp only [graph3,programSubst,consTermSubst,emptySubst]

/-- Proof-only name for the inner existential block of the frozen Run. -/
def runEnd {α : Type} (guard leaf : Program 2) (combine : Program 5)
    (parameter count state finalResults : OTerm α) : Formula α :=
  existsOne
    (graph1 InternalApplicationResultStack.emptyState (.var (.inr (0 : Fin 1)))
        (finalResults.relabel Sum.inl) ⊓
      graph3 (InternalParameterizedApplicationResultStack.iterateP guard leaf combine)
        (.var (.inr (0 : Fin 1))) (count.relabel Sum.inl) (state.relabel Sum.inl) (parameter.relabel Sum.inl))

@[simp] theorem graph1Subst {α β : Type} (p : Program 1)
    (out x : OTerm α) (ts : α → OTerm β) :
    (graph1 p out x).subst (fun a => emb (ts a)) =
      graph1 p (out.subst ts) (x.subst ts) := by
  simp only [graph1,programSubst,consTermSubst,emptySubst]

theorem runEndSubst {α β : Type} (guard leaf : Program 2) (combine : Program 5)
    (parameter count state finalResults : OTerm α) (ts : α → OTerm β) :
    (runEnd guard leaf combine parameter count state finalResults).subst (fun a => emb (ts a)) =
      runEnd guard leaf combine (parameter.subst ts) (count.subst ts) (state.subst ts) (finalResults.subst ts) := by
  unfold runEnd
  rw [existsSubst,liftedEmbedding,conjunctionSubst]
  simp only [graph1Subst,graph3Subst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem runEndRename {α β : Type} (guard leaf : Program 2) (combine : Program 5)
    (parameter count state finalResults : OTerm α) (j : α → β) :
    (runEnd guard leaf combine parameter count state finalResults).relabel j =
      runEnd guard leaf combine (parameter.relabel j) (count.relabel j) (state.relabel j) (finalResults.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (runEnd guard leaf combine parameter count state finalResults).subst (fun a => emb (.var (j a))) = _
  rw [runEndSubst]
  simp only [← termRelabelAsSubst]

theorem actualRunSubst {α β : Type} (guard leaf : Program 2) (combine : Program 5)
    (parameter count work initialResults finalResults : OTerm α) (ts : α → OTerm β) :
    (run guard leaf combine parameter count work initialResults finalResults).subst (fun a => emb (ts a)) =
      run guard leaf combine (parameter.subst ts) (count.subst ts) (work.subst ts)
        (initialResults.subst ts) (finalResults.subst ts) := by
  change (existsOne (graph2 liveState (.var (.inr (0 : Fin 1)))
    (work.relabel Sum.inl) (initialResults.relabel Sum.inl) ⊓
    runEnd guard leaf combine (parameter.relabel Sum.inl) (count.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
      (finalResults.relabel Sum.inl))).subst (fun a => emb (ts a)) = _
  rw [existsSubst,liftedEmbedding,conjunctionSubst]
  simp only [graph2Subst,runEndSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem actualRunRename {α β : Type} (guard leaf : Program 2) (combine : Program 5)
    (parameter count work initialResults finalResults : OTerm α) (j : α → β) :
    (run guard leaf combine parameter count work initialResults finalResults).relabel j =
      run guard leaf combine (parameter.relabel j) (count.relabel j) (work.relabel j)
        (initialResults.relabel j) (finalResults.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (run guard leaf combine parameter count work initialResults finalResults).subst
    (fun a => emb (.var (j a))) = _
  rw [actualRunSubst]
  simp only [← termRelabelAsSubst]

theorem runEndInstance {α : Type} (guard leaf : Program 2) (combine : Program 5)
    (parameter count state finalResults finalState : OTerm α) :
    instantiate (graph1 InternalApplicationResultStack.emptyState (.var (.inr (0 : Fin 1)))
        (finalResults.relabel Sum.inl) ⊓
      graph3 (InternalParameterizedApplicationResultStack.iterateP guard leaf combine)
        (.var (.inr (0 : Fin 1))) (count.relabel Sum.inl) (state.relabel Sum.inl) (parameter.relabel Sum.inl)) (emb finalState) =
      graph1 InternalApplicationResultStack.emptyState finalState finalResults ⊓
        graph3 (InternalParameterizedApplicationResultStack.iterateP guard leaf combine) finalState count state parameter := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [graph1Subst,graph3Subst,liftBind,varBind]

theorem actualRunInstance {α : Type} (guard leaf : Program 2) (combine : Program 5)
    (parameter count work initialResults finalResults state : OTerm α) :
    instantiate (graph2 liveState (.var (.inr (0 : Fin 1)))
        (work.relabel Sum.inl) (initialResults.relabel Sum.inl) ⊓
      runEnd guard leaf combine (parameter.relabel Sum.inl) (count.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
        (finalResults.relabel Sum.inl)) (emb state) =
      graph2 liveState state work initialResults ⊓ runEnd guard leaf combine parameter count state finalResults := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [graph2Subst,runEndSubst,liftBind,varBind]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionSyntaxProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionSyntaxProof
