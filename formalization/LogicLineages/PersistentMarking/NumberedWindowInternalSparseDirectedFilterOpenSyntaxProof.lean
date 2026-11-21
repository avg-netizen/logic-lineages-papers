module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqnRelabel eqnSubst bindEmbedding liftBind varBind zRelabel sucRelabel zSubst sucSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename quadInputsRename)
open NumberedWindowInternalSparseDirectedSeen (scanGraph scanTape)
open NumberedWindowInternalSparseDirectedFilter

attribute [local irreducible] programGraph

private theorem orRename {α β : Type} (p q : Formula α) (j : α → β) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

private theorem orSubst {α β : Type} (p q : Formula α) (ts : α → Term β) :
    (p ⊔ q).subst ts = p.subst ts ⊔ q.subst ts := rfl

private theorem notRename {α β : Type} (p : Formula α) (j : α → β) :
    p.not.relabel j = (p.relabel j).not := rfl

private theorem notSubst {α β : Type} (p : Formula α) (ts : α → Term β) :
    p.not.subst ts = (p.subst ts).not := rfl

private theorem graph4Rename {α β : Type} (p : Program 4) (o a b c d : OTerm α) (j : α → β) :
    (programGraph p o ![a,b,c,d]).relabel j =
      programGraph p (o.relabel j) ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] := by
  rw [programRename,quadInputsRename]

private theorem graph4Subst {α β : Type} (p : Program 4) (o a b c d : OTerm α) (t : α → OTerm β) :
    (programGraph p o ![a,b,c,d]).subst (fun x => emb (t x)) =
      programGraph p (o.subst t) ![a.subst t,b.subst t,c.subst t,d.subst t] := by
  have tape : (fun i => ((![a,b,c,d] : Fin 4 → OTerm α) i).subst t) =
      ![a.subst t,b.subst t,c.subst t,d.subst t] := by
    funext i
    refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => Fin.cases ?_ (fun w =>
      Fin.cases ?_ (fun k => Fin.elim0 k) w) y) x) i <;> rfl
  rw [programSubst,tape]

private theorem cellRename {α β : Type} (o h t : OTerm α) (j : α → β) :
    (cell o h t).relabel j = cell (o.relabel j) (h.relabel j) (t.relabel j) := by
  simp only [cell,programRename,binaryInputsRename]

private theorem cellSubst {α β : Type} (o h tail : OTerm α) (ts : α → OTerm β) :
    (cell o h tail).subst (fun a => emb (ts a)) =
      cell (o.subst ts) (h.subst ts) (tail.subst ts) := by
  have tape : (fun i => ((![h,tail] : Fin 2 → OTerm α) i).subst ts) =
      ![h.subst ts,tail.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold cell
  rw [programSubst,tape]

private theorem rowRename {α β : Type} (E : Program 4)
    (o h tail rest seen ctx ty : OTerm α) (j : α → β) :
    (restRow E o h tail rest seen ctx ty).relabel j =
      restRow E (o.relabel j) (h.relabel j) (tail.relabel j) (rest.relabel j)
        (seen.relabel j) (ctx.relabel j) (ty.relabel j) := by
  simp only [restRow,conjunctionRename,orRename,notRename,cellRename,eqnRelabel,
    passGraph,passTape,scanGraph,scanTape,graph4Rename,sucRelabel,zRelabel]

private theorem rowSubst {α β : Type} (E : Program 4)
    (o h tail rest seen ctx ty : OTerm α) (ts : α → OTerm β) :
    (restRow E o h tail rest seen ctx ty).subst (fun a => emb (ts a)) =
      restRow E (o.subst ts) (h.subst ts) (tail.subst ts) (rest.subst ts)
        (seen.subst ts) (ctx.subst ts) (ty.subst ts) := by
  simp only [restRow,conjunctionSubst,orSubst,notSubst,cellSubst,eqnSubst,
    passGraph,passTape,scanGraph,scanTape,graph4Subst,sucSubst,zSubst]

abbrev reportBinder (E : Program 4) {α : Type} (o h tail seen ctx ty : OTerm α) : Formula (α ⊕ Fin 1) :=
  restRow E (o.relabel Sum.inl) (h.relabel Sum.inl) (tail.relabel Sum.inl) (.var (.inr 0))
    (seen.relabel Sum.inl) (ctx.relabel Sum.inl) (ty.relabel Sum.inl)

theorem reportUnfold (E : Program 4) {α : Type} (o h tail seen ctx ty : OTerm α) :
    restReport E o h tail seen ctx ty = existsOne (reportBinder E o h tail seen ctx ty) := rfl

theorem reportInstance (E : Program 4) {α : Type} (o h tail rest seen ctx ty : OTerm α) :
    instantiate (reportBinder E o h tail seen ctx ty) (emb rest) = restRow E o h tail rest seen ctx ty := by
  simp only [instantiate,reportBinder,bindEmbedding,rowSubst,liftBind,varBind]

theorem reportRename {α β : Type} (E : Program 4) (o h tail seen ctx ty : OTerm α) (j : α → β) :
    (restReport E o h tail seen ctx ty).relabel j =
      restReport E (o.relabel j) (h.relabel j) (tail.relabel j) (seen.relabel j)
        (ctx.relabel j) (ty.relabel j) := by
  rw [reportUnfold,reportUnfold,existsRename]
  unfold reportBinder
  rw [rowRename]
  simp only [Term.relabel_relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof
