module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding allBlockSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst witnessLift)
open ID1Completion.InternalTermSubstitutionProof (actualUniversalSubstitution)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb suc bindEmbedding liftBind varBind sucSubst sucRelabel nextEmbedding)
open ID1Completion.InternalAdditionLawsProof (impSubst liftNext varNext)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedSubst)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets

attribute [local irreducible] programGraph
variable {α β : Type}

private theorem axisSubst (xs ys : OTerm α) (ts : α → OTerm β) :
    (axisInclusion xs ys).subst (fun a => emb (ts a)) =
      axisInclusion (xs.subst ts) (ys.subst ts) := by
  unfold axisInclusion
  rw [actualUniversalSubstitution,liftedEmbedding,impSubst,memberSubst,memberSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem depthComparedSubst (d D H K M : OTerm α) (w : Fin 6 → OTerm α) (ts : α → OTerm β) :
    (depthCompared d D H K M w).subst (fun a => emb (ts a)) =
      depthCompared (d.subst ts) (D.subst ts) (H.subst ts) (K.subst ts) (M.subst ts)
        (fun i => (w i).subst ts) := by
  unfold depthCompared
  rw [impSubst,conjunctionSubst]
  rw [observedSubst d H K M (w 0) (w 1) (w 2) ts,
    observedSubst D H K M (w 3) (w 4) (w 5) ts]
  simp only [pairInclusion,conjunctionSubst,axisSubst]

private theorem depthSubst (d D H K M : OTerm α) (ts : α → OTerm β) :
    (depthAt d D H K M).subst (fun a => emb (ts a)) =
      depthAt (d.subst ts) (D.subst ts) (H.subst ts) (K.subst ts) (M.subst ts) := by
  unfold depthAt depthMatrix
  rw [allBlockSubst,liftedEmbedding,depthComparedSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem depthRename (d D H K M : OTerm α) (j : α → β) :
    (depthAt d D H K M).relabel j =
      depthAt (d.relabel j) (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (depthAt d D H K M).subst (fun a => emb (.var (j a))) = _
  rw [depthSubst]
  simp only [← termRelabelAsSubst]

theorem adjacentRename (d H K M : OTerm α) (j : α → β) :
    (adjacentAt d H K M).relabel j =
      adjacentAt (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) := by
  unfold adjacentAt
  rw [depthRename,sucRelabel]

theorem adjacentInstance (d H K M : OTerm α) :
    instantiate (adjacentMotive H K M) (emb d) = adjacentAt d H K M := by
  simp only [instantiate,bindEmbedding,adjacentMotive,adjacentAt,depthSubst,sucSubst,liftBind,varBind]

theorem adjacentNext (H K M : OTerm α) :
    successorInstance (adjacentMotive H K M) =
      adjacentAt (suc (.var (.inr 0))) (H.relabel Sum.inl) (K.relabel Sum.inl) (M.relabel Sum.inl) := by
  simp only [successorInstance,nextEmbedding,adjacentMotive,adjacentAt,depthSubst,sucSubst,liftNext,varNext]

theorem depthWitness (d D H K M : OTerm α) (w : Fin 6 → OTerm α) :
    (depthMatrix d D H K M).subst (Sum.elim Term.var (fun i => emb (w i))) = depthCompared d D H K M w := by
  have he : Sum.elim Term.var (fun i => emb (w i)) = (fun x => emb (Sum.elim Term.var w x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold depthMatrix
  rw [depthComparedSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof
