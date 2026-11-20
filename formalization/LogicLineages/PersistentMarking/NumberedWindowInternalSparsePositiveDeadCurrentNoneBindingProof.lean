module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentNoneBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind zSubst zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseFieldInductionTargets (atCode atIndex)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph finishRename)

attribute [local irreducible] programGraph finish

private theorem argsSubst {α β : Type} (ctx ty current cert : OTerm α) (ts : α → OTerm β) :
    (fun i => (args4 ctx ty current cert i).subst ts) =
      args4 (ctx.subst ts) (ty.subst ts) (current.subst ts) (cert.subst ts) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun i => Fin.elim0 i) c) b) a) i <;> rfl

private theorem finishSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (out ctx ty current cert : OTerm α) (ts : α → OTerm β) :
    (finishGraph raw least out ctx ty current cert).subst (fun a => emb (ts a)) =
      finishGraph raw least (out.subst ts) (ctx.subst ts) (ty.subst ts) (current.subst ts) (cert.subst ts) := by
  unfold finishGraph
  rw [programSubst,argsSubst] <;> rfl

def noneMotive {α : Type} (raw : Program 5) (least : Program 3) (ctx ty : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  finishGraph raw least z (ctx.relabel Sum.inl) (ty.relabel Sum.inl) z (.var (.inr 0))

theorem noneAt {α : Type} (raw : Program 5) (least : Program 3) (ctx ty cert : OTerm α) :
    atCode (noneMotive raw least ctx ty) cert = finishGraph raw least z ctx ty z cert := by
  simp only [atCode,noneMotive,instantiate,bindEmbedding,finishSubst,zSubst,liftBind,varBind]

theorem noneIndex {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty : OTerm α) (i : Fin 3) :
    atIndex (noneMotive raw least ctx ty) i =
      finishGraph raw least z (ctx.relabel Sum.inl) (ty.relabel Sum.inl) z (.var (.inr i)) := by
  unfold atIndex noneMotive
  rw [finishRename]
  simp only [zRelabel,Term.relabel_relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentNoneBindingProof
