module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel sucSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename consGraphSubst)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (quadRename)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (finishAtRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof (blockRename)

private theorem argsSubst {α β : Type} (a b c d : OTerm α) (ts : α → OTerm β) :
    (fun i => (args4 a b c d i).subst ts) = args4 (a.subst ts) (b.subst ts) (c.subst ts) (d.subst ts) := by
  funext i
  refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => Fin.cases ?_ (fun w =>
    Fin.cases ?_ (fun k => Fin.elim0 k) w) y) x) i <;> rfl

theorem graph4Subst {α β : Type} (p : Program 4) (out a b c d : OTerm α) (ts : α → OTerm β) :
    (programGraph p out (args4 a b c d)).subst (fun x => emb (ts x)) =
      programGraph p (out.subst ts) (args4 (a.subst ts) (b.subst ts) (c.subst ts) (d.subst ts)) := by
  rw [programSubst,argsSubst]

theorem dataRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target head tail next : OTerm α) (j : α → β) :
    (headData raw least ctx ty source cert target head tail next).relabel j =
      headData raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j) (target.relabel j)
        (head.relabel j) (tail.relabel j) (next.relabel j) := by
  simp only [headData,selectedGraph,conjunctionRename,consGraphRename,quadRename,sucRelabel,finishAtRename]

theorem acceptedHeadRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) (j : α → β) :
    (hasAcceptedHead raw least ctx ty source cert target).relabel j =
      hasAcceptedHead raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
        (cert.relabel j) (target.relabel j) := by
  simp only [hasAcceptedHead,blockRename,headRow,dataRename,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem witnessLift {α : Type} (t : OTerm α) (ts : Fin 3 → OTerm α) :
    (t.relabel Sum.inl).subst (Sum.elim Term.var ts) = t := by
  rw [termRelabelSubst]
  exact termSubstVar t

abbrev headValues {α : Type} (head tail next : OTerm α) : Fin 3 → OTerm α := ![head,tail,next]

theorem rowWitness {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target head tail next : OTerm α) :
    (headRow raw least ctx ty source cert target).subst
        (Sum.elim Term.var (fun i => emb (headValues head tail next i))) =
      headData raw least ctx ty source cert target head tail next := by
  let xs := headValues head tail next
  have h : (Sum.elim Term.var (fun i => emb (xs i))) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext a
    cases a <;> rfl
  change (headRow raw least ctx ty source cert target).subst (Sum.elim Term.var (fun i => emb (xs i))) = _
  rw [h]
  simp only [headRow,headData,selectedGraph,finishAt,conjunctionSubst,consGraphSubst,graph4Subst,
    witnessLift,sucSubst,Term.subst,Sum.elim_inr] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof
