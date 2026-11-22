module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb z suc bindEmbedding liftBind varBind sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalCoverCartesianFoldTargets (imageGraph)
open NumberedWindowInternalCoverCartesianFoldSyntaxProof (imageRename)
open NumberedWindowInternalCoverCartesianFoldOriginTargets

variable {k : Nat} {α β : Type}

private theorem mapCons (a : OTerm α) (ps : Fin k → OTerm α) (ts : α → OTerm β) :
    (fun i : Fin (k+1) => ((Fin.cons a ps : Fin (k+1) → OTerm α) i).subst ts) =
      Fin.cons (a.subst ts) (fun i => (ps i).subst ts) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem blockHitRename (D : Program (k+1)) (source image : OTerm α)
    (params : Fin k → OTerm α) (j : α → β) :
    (blockHit D source image params).relabel j =
      blockHit D (source.relabel j) (image.relabel j) (fun i => (params i).relabel j) := by
  simp only [blockHit,programRename,consTermRename,sucRelabel,zRelabel]

private theorem blockHitSubst (D : Program (k+1)) (source image : OTerm α)
    (params : Fin k → OTerm α) (ts : α → OTerm β) :
    (blockHit D source image params).subst (fun a => emb (ts a)) =
      blockHit D (source.subst ts) (image.subst ts) (fun i => (params i).subst ts) := by
  unfold blockHit
  rw [programSubst,sucSubst,zSubst,mapCons,mapCons]

private theorem rowRename (D : Program (k+1)) (raw source image : OTerm α)
    (params : Fin k → OTerm α) (j : α → β) :
    (originRow D raw source image params).relabel j =
      originRow D (raw.relabel j) (source.relabel j) (image.relabel j) (fun i => (params i).relabel j) := by
  simp only [originRow,conjunctionRename,graphRename,blockHitRename]

private theorem rowSubst (D : Program (k+1)) (raw source image : OTerm α)
    (params : Fin k → OTerm α) (ts : α → OTerm β) :
    (originRow D raw source image params).subst (fun a => emb (ts a)) =
      originRow D (raw.subst ts) (source.subst ts) (image.subst ts) (fun i => (params i).subst ts) := by
  simp only [originRow,conjunctionSubst,memberSubst,blockHitSubst]

theorem originInstance (D : Program (k+1)) (raw source image : OTerm α)
    (params : Fin k → OTerm α) :
    instantiate (originBinder D raw image params) (emb source) = originRow D raw source image params := by
  simp only [instantiate,originBinder,bindEmbedding,rowSubst,liftBind,varBind]

theorem originRename (D : Program (k+1)) (raw image : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (hasOrigin D raw image params).relabel j =
      hasOrigin D (raw.relabel j) (image.relabel j) (fun i => (params i).relabel j) := by
  unfold hasOrigin
  rw [existsRename]
  unfold originBinder
  rw [rowRename]
  simp only [Term.relabel_relabel] <;> rfl

private theorem originSubst (D : Program (k+1)) (raw image : OTerm α) (params : Fin k → OTerm α)
    (ts : α → OTerm β) :
    (hasOrigin D raw image params).subst (fun a => emb (ts a)) =
      hasOrigin D (raw.subst ts) (image.subst ts) (fun i => (params i).subst ts) := by
  unfold hasOrigin
  rw [existsSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

private theorem imageSubst (D : Program (k+1)) (raw image : OTerm α)
    (params : Fin k → OTerm α) (ts : α → OTerm β) :
    (imageGraph D raw image params).subst (fun a => emb (ts a)) =
      imageGraph D (raw.subst ts) (image.subst ts) (fun i => (params i).subst ts) := by
  unfold imageGraph
  rw [programSubst,sucSubst,zSubst,mapCons,mapCons]

abbrev originAt (D : Program (k+1)) (raw image : OTerm α) (params : Fin k → OTerm α) : Formula α :=
  (imageGraph D raw image params).imp (hasOrigin D raw image params)

theorem originAtRename (D : Program (k+1)) (raw image : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (originAt D raw image params).relabel j =
      originAt D (raw.relabel j) (image.relabel j) (fun i => (params i).relabel j) := by
  change ((imageGraph D raw image params).relabel j).imp ((hasOrigin D raw image params).relabel j) = _
  rw [imageRename,originRename]

private theorem originAtSubst (D : Program (k+1)) (raw image : OTerm α)
    (params : Fin k → OTerm α) (ts : α → OTerm β) :
    (originAt D raw image params).subst (fun a => emb (ts a)) =
      originAt D (raw.subst ts) (image.subst ts) (fun i => (params i).subst ts) := by
  simp only [originAt,impSubst,imageSubst,originSubst]

abbrev motive (D : Program (k+1)) (image : OTerm α) (params : Fin k → OTerm α) : Formula (α ⊕ Fin 1) :=
  originAt D (.var (.inr 0)) (image.relabel Sum.inl) (fun i => (params i).relabel Sum.inl)

theorem atCodeEq (D : Program (k+1)) (raw image : OTerm α) (params : Fin k → OTerm α) :
    atCode (motive D image params) raw = originAt D raw image params := by
  rw [atCode,instantiate,bindEmbedding]
  change (originAt D (.var (.inr 0)) (image.relabel Sum.inl) (fun i => (params i).relabel Sum.inl)).subst _ = _
  rw [originAtSubst]
  simp only [liftBind,varBind]

theorem atIndexEq (D : Program (k+1)) (image : OTerm α) (params : Fin k → OTerm α) (i : Fin 3) :
    atIndex (motive D image params) i = originAt D (.var (.inr i))
      (image.relabel Sum.inl) (fun j => (params j).relabel Sum.inl) := by
  unfold atIndex motive
  rw [originAtRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginSyntaxProof
