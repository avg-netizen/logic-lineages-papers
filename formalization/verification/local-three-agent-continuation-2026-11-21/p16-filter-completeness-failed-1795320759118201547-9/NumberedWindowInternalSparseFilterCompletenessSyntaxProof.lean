module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb bindEmbedding liftBind varBind sucSubst zSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof (graph4Subst)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Subst)
open NumberedWindowInternalSparseDirectedSeen (scanGraph scanTape)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (hitGraph hitRename)

theorem scanSubst {α β : Type} (E : Program 4) (seen ctx ty k : OTerm α) (ts : α → OTerm β) :
    (scanGraph E seen ctx ty k).subst (fun a => emb (ts a)) =
      scanGraph E (seen.subst ts) (ctx.subst ts) (ty.subst ts) (k.subst ts) := by
  simp only [scanGraph,scanTape,graph4Subst,sucSubst,zSubst]

def completeAt {α : Type} (E : Program 4) (vertices seen ctx ty k : OTerm α) : Formula α :=
  (memberGraph vertices k ⊓ scanGraph E seen ctx ty k).imp (hitGraph E vertices seen ctx ty k)

theorem completeRename {α β : Type} (E : Program 4) (vertices seen ctx ty k : OTerm α) (j : α → β) :
    (completeAt E vertices seen ctx ty k).relabel j =
      completeAt E (vertices.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j) (k.relabel j) := by
  change ((memberGraph vertices k).relabel j ⊓ (scanGraph E seen ctx ty k).relabel j).imp
    ((hitGraph E vertices seen ctx ty k).relabel j) = _
  rw [graphRename,scanRename,hitRename]

private theorem completeSubst {α β : Type} (E : Program 4) (vertices seen ctx ty k : OTerm α) (ts : α → OTerm β) :
    (completeAt E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      completeAt E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts) (k.subst ts) := by
  simp only [completeAt,impSubst,conjunctionSubst,memberSubst,scanSubst,hitGraph,graph5Subst,sucSubst,zSubst]

abbrev motive {α : Type} (E : Program 4) (seen ctx ty k : OTerm α) : Formula (α ⊕ Fin 1) :=
  completeAt E (.var (.inr 0)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)

theorem motiveAt {α : Type} (E : Program 4) (vertices seen ctx ty k : OTerm α) :
    atCode (motive E seen ctx ty k) vertices = completeAt E vertices seen ctx ty k := by
  simp only [atCode,motive,instantiate,bindEmbedding,completeSubst,liftBind,varBind]

theorem motiveIndex {α : Type} (E : Program 4) (seen ctx ty k : OTerm α) (i : Fin 3) :
    atIndex (motive E seen ctx ty k) i = completeAt E (.var (.inr i)) (seen.relabel Sum.inl)
      (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex motive
  rw [completeRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

theorem moveHead {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (E : Program 4)
    (out seen ctx ty h k : OTerm α) (same : Derivation body Γ (eqn h k))
    (law : Derivation body Γ ((scanGraph E seen ctx ty h).imp (memberGraph out h))) :
    Nonempty (Derivation body Γ ((scanGraph E seen ctx ty k).imp (memberGraph out k))) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let θ := (scanGraph E (seen.relabel j) (ctx.relabel j) (ty.relabel j) v).imp (memberGraph (out.relabel j) v)
  have inst (x : OTerm α) : instantiate θ (emb x) = (scanGraph E seen ctx ty x).imp (memberGraph out x) := by
    simp only [θ,j,v,instantiate,bindEmbedding,impSubst,scanSubst,memberSubst,liftBind,varBind]
  have lifted := Derivation.equalityElimination θ (emb h) (emb k) same (by rw [inst]; exact law)
  rw [inst] at lifted
  exact ⟨lifted⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessSyntaxProof
