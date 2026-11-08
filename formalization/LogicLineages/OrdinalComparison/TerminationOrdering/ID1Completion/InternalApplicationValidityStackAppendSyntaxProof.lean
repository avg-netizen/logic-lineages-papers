module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms
open InternalRawListRecursionSyntaxProof InternalNumericIterationSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem successStateRename {α β : Type} (j : α → β) :
    (successState : OTerm α).relabel j = (successState : OTerm β) := by
  simp only [successState,sucRelabel,zRelabel]

@[simp] theorem successStateSubst {α β : Type} (ts : α → OTerm β) :
    (successState : OTerm α).subst ts = (successState : OTerm β) := by
  simp only [successState,sucSubst,zSubst]

@[simp] theorem graph2Subst {α β : Type} (p : Program 2)
    (out x y : OTerm α) (ts : α → OTerm β) :
    (graph2 p out x y).subst (fun a => emb (ts a)) =
      graph2 p (out.subst ts) (x.subst ts) (y.subst ts) := by
  simp only [graph2,programSubst,consTermSubst,emptySubst]

theorem appendConsInstance {α : Type} (out head tail suffix result : OTerm α) :
    instantiate
      (graph2 append (.var (.inr (0 : Fin 1))) (tail.relabel Sum.inl) (suffix.relabel Sum.inl) ⊓
        graph2 InternalListCodec.consCode (out.relabel Sum.inl)
          (head.relabel Sum.inl) (.var (.inr (0 : Fin 1)))) (emb result) =
      graph2 append result tail suffix ⊓ graph2 InternalListCodec.consCode out head result := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [graph2Subst,liftBind,varBind]

theorem appendConsSubst {α β : Type} (out head tail suffix : OTerm α) (ts : α → OTerm β) :
    (appendConsStep out head tail suffix).subst (fun a => emb (ts a)) =
      appendConsStep (out.subst ts) (head.subst ts) (tail.subst ts) (suffix.subst ts) := by
  unfold appendConsStep
  rw [existsSubst,liftedEmbedding,conjunctionSubst]
  simp only [graph2Subst,liftSubst,Term.subst,Sum.elim_inr]

theorem appendConsRename {α β : Type} (out head tail suffix : OTerm α) (j : α → β) :
    (appendConsStep out head tail suffix).relabel j =
      appendConsStep (out.relabel j) (head.relabel j) (tail.relabel j) (suffix.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (appendConsStep out head tail suffix).subst (fun a => emb (.var (j a))) = _
  rw [appendConsSubst]
  simp only [← termRelabelAsSubst]

theorem successfulWorkSubst {α β : Type} (node leaf : Program 1)
    (count work : OTerm α) (ts : α → OTerm β) :
    (successfulWork node leaf count work).subst (fun a => emb (ts a)) =
      successfulWork node leaf (count.subst ts) (work.subst ts) := by
  unfold successfulWork
  rw [existsSubst,liftedEmbedding,conjunctionSubst]
  simp only [graph2Subst,liftSubst,Term.subst,Sum.elim_inr,successStateSubst,
    InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem successfulWorkRename {α β : Type} (node leaf : Program 1)
    (count work : OTerm α) (j : α → β) :
    (successfulWork node leaf count work).relabel j =
      successfulWork node leaf (count.relabel j) (work.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (successfulWork node leaf count work).subst (fun a => emb (.var (j a))) = _
  rw [successfulWorkSubst]
  simp only [← termRelabelAsSubst]

theorem successfulWorkInstance {α : Type} (node leaf : Program 1)
    (count work state : OTerm α) :
    instantiate
      (graph2 InternalPairing.pairing (.var (.inr (0 : Fin 1)))
          InternalOriginalStepGuard.one (work.relabel Sum.inl) ⊓
        graph2 (InternalApplicationValidityStack.iterate node leaf) successState
          (count.relabel Sum.inl) (.var (.inr (0 : Fin 1)))) (emb state) =
      graph2 InternalPairing.pairing state InternalOriginalStepGuard.one work ⊓
        graph2 (InternalApplicationValidityStack.iterate node leaf) successState count state := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [graph2Subst,liftBind,varBind,successStateSubst,
    InternalOriginalStepGuard.one,sucSubst,zSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
