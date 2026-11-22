module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureSyntaxProof (liftedEmbedding allBlockSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalTermSubstitutionProof (actualUniversalSubstitution)
open ID1Completion.InternalQuotientComparisonSyntaxProof (orderSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb suc bindEmbedding liftBind varBind sucSubst nextEmbedding)
open ID1Completion.InternalAdditionLawsProof (impSubst liftNext varNext)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets
open NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof (depthComparedSubst)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets

variable {α β : Type}

private theorem depthSubst (d D H K M : OTerm α) (ts : α → OTerm β) :
    (depthAt d D H K M).subst (fun a => emb (ts a)) =
      depthAt (d.subst ts) (D.subst ts) (H.subst ts) (K.subst ts) (M.subst ts) := by
  unfold depthAt depthMatrix
  rw [allBlockSubst,liftedEmbedding,depthComparedSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

private theorem guardSubst (d D H K M : OTerm α) (ts : α → OTerm β) :
    (depthGuard d D H K M).subst (fun a => emb (ts a)) =
      depthGuard (d.subst ts) (D.subst ts) (H.subst ts) (K.subst ts) (M.subst ts) := by
  unfold depthGuard
  rw [impSubst,orderSubst,sucSubst,depthSubst]

private theorem lowerSubst (D H K M : OTerm α) (ts : α → OTerm β) :
    (allLower D H K M).subst (fun a => emb (ts a)) =
      allLower (D.subst ts) (H.subst ts) (K.subst ts) (M.subst ts) := by
  unfold allLower lowerMatrix
  rw [actualUniversalSubstitution,liftedEmbedding,guardSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem lowerRename (D H K M : OTerm α) (j : α → β) :
    (allLower D H K M).relabel j =
      allLower (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (allLower D H K M).subst (fun a => emb (.var (j a))) = _
  rw [lowerSubst]
  simp only [← termRelabelAsSubst]

theorem lowerInstance (d D H K M : OTerm α) :
    instantiate (lowerMatrix D H K M) (emb d) = depthGuard d D H K M := by
  simp only [instantiate,bindEmbedding,lowerMatrix,guardSubst,liftBind,varBind]

theorem upperInstance (D H K M : OTerm α) :
    instantiate (upperMotive H K M) (emb D) = allLower D H K M := by
  simp only [instantiate,bindEmbedding,upperMotive,lowerSubst,liftBind,varBind]

theorem upperNext (H K M : OTerm α) :
    successorInstance (upperMotive H K M) =
      allLower (suc (.var (.inr 0))) (H.relabel Sum.inl) (K.relabel Sum.inl) (M.relabel Sum.inl) := by
  simp only [successorInstance,nextEmbedding,upperMotive,lowerSubst,liftNext,varNext]

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthSyntaxProof
