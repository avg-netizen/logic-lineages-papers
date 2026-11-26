module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding varBind liftBind sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalEqualityTest (equalityTest)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename graph5Subst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseDirectedFilter (pass)

attribute [local irreducible] programGraph

/-- The unchanged physical pass read on [vertices,seen,ctx,ty,candidate].
The candidate slot is ignored; nothing is recomputed. -/
def passed (E : Program 4) : Program 5 :=
  .composition (pass E) ![.projection 0,.projection 1,.projection 2,.projection 3]

/-- The actual scratch membership bit of the actual pass output at the
candidate in slot 4. Program totality selects the one filtered output. -/
def memberOfPass (E : Program 4) : Program 5 :=
  .composition scratchMember ![passed E,.projection 4]

def hitGraph (E : Program 4) {α : Type} (vertices seen ctx ty k : OTerm α) : Formula α :=
  programGraph (memberOfPass E) (suc z) ![vertices,seen,ctx,ty,k]

/-- The induction invariant at one scratch code: occurrence in the pass
output of this code gives occurrence in this same code. -/
def included (E : Program 4) {α : Type} (vertices seen ctx ty k : OTerm α) : Formula α :=
  (hitGraph E vertices seen ctx ty k).imp (memberGraph vertices k)

/-- The actual head equality test of the membership row returns zero. -/
def missGraph {α : Type} (h k : OTerm α) : Formula α :=
  programGraph equalityTest z ![h,k]

theorem hitRename (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α) (j : α → β) :
    (hitGraph E vertices seen ctx ty k).relabel j =
      hitGraph E (vertices.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j)
        (k.relabel j) := by
  unfold hitGraph
  rw [graph5Rename,sucRelabel,zRelabel]

private theorem hitSubst (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (ts : α → OTerm β) :
    (hitGraph E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      hitGraph E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts)
        (k.subst ts) := by
  unfold hitGraph
  rw [graph5Subst,sucSubst,zSubst]

private theorem memberSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) =
      memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

theorem includedRename (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (j : α → β) :
    (included E vertices seen ctx ty k).relabel j =
      included E (vertices.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j)
        (k.relabel j) := by
  change ((hitGraph E vertices seen ctx ty k).relabel j).imp
    ((memberGraph vertices k).relabel j) = _
  rw [hitRename,graphRename] <;> rfl

private theorem includedSubst (E : Program 4) {α β : Type} (vertices seen ctx ty k : OTerm α)
    (ts : α → OTerm β) :
    (included E vertices seen ctx ty k).subst (fun a => emb (ts a)) =
      included E (vertices.subst ts) (seen.subst ts) (ctx.subst ts) (ty.subst ts)
        (k.subst ts) := by
  simp only [included,impSubst,hitSubst,memberSubst]

theorem missRename {α β : Type} (h k : OTerm α) (j : α → β) :
    (missGraph h k).relabel j = missGraph (h.relabel j) (k.relabel j) := by
  unfold missGraph
  rw [programRename,binaryInputsRename,zRelabel]

theorem missNotRename {α β : Type} (h k : OTerm α) (j : α → β) :
    (missGraph h k).not.relabel j = (missGraph (h.relabel j) (k.relabel j)).not := by
  change ((missGraph h k).relabel j).not = _
  rw [missRename]

theorem splitRename {α β : Type} (h tail k : OTerm α) (j : α → β) :
    ((missGraph h k).not ⊔ memberGraph tail k).relabel j =
      (missGraph (h.relabel j) (k.relabel j)).not ⊔
        memberGraph (tail.relabel j) (k.relabel j) := by
  change ((missGraph h k).relabel j).not ⊔ (memberGraph tail k).relabel j = _
  rw [missRename,graphRename]

/-- Edge program, seen, context, type and candidate are fixed parameters;
only the original scratch vertices code is generalized. -/
abbrev invariant (E : Program 4) {α : Type} (seen ctx ty k : OTerm α) : Formula (α ⊕ Fin 1) :=
  included E (.var (.inr 0)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl)
    (ty.relabel Sum.inl) (k.relabel Sum.inl)

theorem invariantCode (E : Program 4) {α : Type} (seen ctx ty k n : OTerm α) :
    atCode (invariant E seen ctx ty k) n = included E n seen ctx ty k := by
  rw [atCode,instantiate,bindEmbedding]
  change (included E (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (seen.relabel Sum.inl)
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)).subst _ = _
  rw [includedSubst]
  simp only [liftBind,varBind]

theorem invariantIndex (E : Program 4) {α : Type} (seen ctx ty k : OTerm α) (i : Fin 3) :
    atIndex (invariant E seen ctx ty k) i =
      included E (.var (.inr i)) (seen.relabel Sum.inl) (ctx.relabel Sum.inl)
        (ty.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex
  change (included E (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (seen.relabel Sum.inl)
    (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (k.relabel Sum.inl)).relabel _ = _
  rw [includedRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
