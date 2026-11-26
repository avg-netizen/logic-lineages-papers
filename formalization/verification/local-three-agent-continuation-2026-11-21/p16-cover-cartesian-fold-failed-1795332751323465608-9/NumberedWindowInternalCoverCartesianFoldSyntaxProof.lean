module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionSyntaxProof (graphSubst)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel emb bindEmbedding liftBind varBind sucSubst zSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalCoverCartesianFoldTargets

variable {k : Nat} {α β : Type}

theorem flatRename (D : Program (k+1)) (out raw : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (flatGraph D out raw params).relabel j =
      flatGraph D (out.relabel j) (raw.relabel j) (fun i => (params i).relabel j) := by
  simp only [flatGraph,programRename,consTermRename]

theorem imageRename (D : Program (k+1)) (raw image : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (imageGraph D raw image params).relabel j =
      imageGraph D (raw.relabel j) (image.relabel j) (fun i => (params i).relabel j) := by
  simp only [imageGraph,programRename,consTermRename,sucRelabel,zRelabel]

private theorem mapCons (a : OTerm α) (ps : Fin k → OTerm α) (ts : α → OTerm β) :
    (fun i : Fin (k+1) => (Fin.cons a ps i).subst ts) = Fin.cons (a.subst ts) (fun i => (ps i).subst ts) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem imageSubst (D : Program (k+1)) (raw image : OTerm α) (params : Fin k → OTerm α) (ts : α → OTerm β) :
    (imageGraph D raw image params).subst (fun a => emb (ts a)) =
      imageGraph D (raw.subst ts) (image.subst ts) (fun i => (params i).subst ts) := by
  unfold imageGraph programGraph
  rw [graphSubst,sucSubst,zSubst,mapCons,mapCons]

def atList (D : Program (k+1)) (raw source image : OTerm α) (params : Fin k → OTerm α) : Formula α :=
  (memberGraph raw source).imp (imageGraph D raw image params)

theorem atListRename (D : Program (k+1)) (raw source image : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (atList D raw source image params).relabel j =
      atList D (raw.relabel j) (source.relabel j) (image.relabel j) (fun i => (params i).relabel j) := by
  change ((memberGraph raw source).relabel j).imp ((imageGraph D raw image params).relabel j) = _
  rw [graphRename,imageRename]
  rfl

private theorem atListSubst (D : Program (k+1)) (raw source image : OTerm α) (params : Fin k → OTerm α)
    (ts : α → OTerm β) :
    (atList D raw source image params).subst (fun a => emb (ts a)) =
      atList D (raw.subst ts) (source.subst ts) (image.subst ts) (fun i => (params i).subst ts) := by
  simp only [atList,impSubst,memberSubst,imageSubst]

abbrev motive (D : Program (k+1)) (source image : OTerm α) (params : Fin k → OTerm α) : Formula (α ⊕ Fin 1) :=
  atList D (.var (.inr 0)) (source.relabel Sum.inl) (image.relabel Sum.inl) (fun i => (params i).relabel Sum.inl)

theorem atCodeEq (D : Program (k+1)) (raw source image : OTerm α) (params : Fin k → OTerm α) :
    atCode (motive D source image params) raw = atList D raw source image params := by
  simp only [atCode,motive,instantiate,bindEmbedding,atListSubst,liftBind,varBind]

theorem atIndexEq (D : Program (k+1)) (source image : OTerm α) (params : Fin k → OTerm α) (i : Fin 3) :
    atIndex (motive D source image params) i = atList D (.var (.inr i))
      (source.relabel Sum.inl) (image.relabel Sum.inl) (fun j => (params j).relabel Sum.inl) := by
  unfold atIndex motive
  rw [atListRename]
  simp only [Term.relabel_relabel,Term.relabel]
  rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
