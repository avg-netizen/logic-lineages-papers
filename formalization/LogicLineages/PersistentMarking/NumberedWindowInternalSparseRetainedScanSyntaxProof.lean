module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding varBind liftBind sucSubst zSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Subst)
open NumberedWindowInternalSparseDirectedSeen (scanGraph scanTape)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (hitGraph hitRename)

attribute [local irreducible] programGraph

/-- The induction invariant at one scratch vertices code: a member of the
actual pass output of this code passed the original scan against the
same fixed seen list, context and type. -/
def hitScan (E : Program 4) {α : Type} (vertices seen ctx ty k : OTerm α) : Formula α :=
  (hitGraph E vertices seen ctx ty k).imp (scanGraph E seen ctx ty k)

private theorem hitSubst (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (ts : α → OTerm β) :
    (hitGraph E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      hitGraph E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts)
        (k.subst ts) := by
  unfold hitGraph
  rw [graph5Subst,sucSubst,zSubst]

private theorem scanSubst (E : Program 4) {α β : Type} (seen ctx ty v : OTerm α)
    (ts : α → OTerm β) :
    (scanGraph E seen ctx ty v).subst (fun a => emb (ts a)) =
      scanGraph E (seen.subst ts) (ctx.subst ts) (ty.subst ts) (v.subst ts) := by
  have tape : (fun i => ((![seen,ctx,ty,v] : Fin 4 → OTerm α) i).subst ts) =
      ![seen.subst ts,ctx.subst ts,ty.subst ts,v.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => Fin.cases ?_ (fun w =>
      Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) w) y) x) i <;> rfl
  simp only [scanGraph,scanTape,programSubst,tape,sucSubst,zSubst]

theorem hitScanRename (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (j : α → β) :
    (hitScan E vertices seen ctx ty k).relabel j =
      hitScan E (vertices.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j)
        (k.relabel j) := by
  change ((hitGraph E vertices seen ctx ty k).relabel j).imp
    ((scanGraph E seen ctx ty k).relabel j) = _
  rw [hitRename,scanRename] <;> rfl

private theorem hitScanSubst (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (ts : α → OTerm β) :
    (hitScan E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      hitScan E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts)
        (k.subst ts) := by
  simp only [hitScan,impSubst,hitSubst,scanSubst]

/-- Edge program, seen, context, type and candidate are fixed parameters;
only the original scratch vertices code is generalized. -/
abbrev scanInvariant (E : Program 4) {α : Type} (seen ctx ty k : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  hitScan E (.var (.inr 0)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl)
    (ty.relabel Sum.inl) (k.relabel Sum.inl)

theorem scanInvariantCode (E : Program 4) {α : Type} (seen ctx ty k n : OTerm α) :
    atCode (scanInvariant E seen ctx ty k) n = hitScan E n seen ctx ty k := by
  rw [atCode,instantiate,bindEmbedding]
  change (hitScan E (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (seen.relabel Sum.inl)
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)).subst _ = _
  rw [hitScanSubst]
  simp only [liftBind,varBind]

theorem scanInvariantIndex (E : Program 4) {α : Type} (seen ctx ty k : OTerm α) (i : Fin 3) :
    atIndex (scanInvariant E seen ctx ty k) i =
      hitScan E (.var (.inr i)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl)
        (ty.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex
  change (hitScan E (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (seen.relabel Sum.inl)
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)).relabel _ = _
  rw [hitScanRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanSyntaxProof
