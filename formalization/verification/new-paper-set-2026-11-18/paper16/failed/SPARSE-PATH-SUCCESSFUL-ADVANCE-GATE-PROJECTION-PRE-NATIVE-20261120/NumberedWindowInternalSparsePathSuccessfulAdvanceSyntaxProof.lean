module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel sucSubst zSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (hopCertified suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (quadRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof (blockRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof

theorem acceptsRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current hop target : OTerm α) (j : α → β) :
    (selectedGraph raw least (suc target) ctx ty (suc current) hop).relabel j =
      selectedGraph raw least (suc (target.relabel j)) (ctx.relabel j) (ty.relabel j)
        (suc (current.relabel j)) (hop.relabel j) := by
  unfold selectedGraph
  simp only [quadRename,sucRelabel]

theorem fieldsRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current hop target q w r : OTerm α) (j : α → β) :
    (hopCalls raw least ctx ty current hop target q w r).relabel j =
      hopCalls raw least (ctx.relabel j) (ty.relabel j) (current.relabel j) (hop.relabel j)
        (target.relabel j) (q.relabel j) (w.relabel j) (r.relabel j) := by
  simp only [hopCalls,hopCertified,actualCalls,conjunctionRename,unaryRename,graph3Rename,graph5Rename,sucRelabel,zRelabel]

theorem reportRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current hop target : OTerm α) (j : α → β) :
    (someHopCalls raw least ctx ty current hop target).relabel j =
      someHopCalls raw least (ctx.relabel j) (ty.relabel j) (current.relabel j)
        (hop.relabel j) (target.relabel j) := by
  simp only [someHopCalls,blockRename,hopCallRow,fieldsRename,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem witnessLift {α : Type} (n : OTerm α) (xs : Fin 3 → OTerm α) :
    (n.relabel Sum.inl).subst (Sum.elim Term.var xs) = n := by
  rw [termRelabelSubst]
  exact termSubstVar n

abbrev reports {α : Type} (q w r : OTerm α) : Fin 3 → OTerm α := ![q,w,r]

theorem rowWitness {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current hop target q w r : OTerm α) :
    (hopCallRow raw least ctx ty current hop target).subst
        (Sum.elim Term.var (fun i => emb (reports q w r i))) =
      hopCalls raw least ctx ty current hop target q w r := by
  let xs := reports q w r
  have h : (Sum.elim Term.var (fun i => emb (xs i))) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext a
    cases a <;> rfl
  change (hopCallRow raw least ctx ty current hop target).subst (Sum.elim Term.var (fun i => emb (xs i))) = _
  rw [h]
  simp only [hopCallRow,hopCalls,hopCertified,actualCalls,conjunctionSubst,unarySubst,graph3Subst,
    graph5Subst,witnessLift,sucSubst,zSubst,Term.subst,Sum.elim_inr] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof
