module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding liftBind varBind sucSubst zSubst sucRelabel zRelabel)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (allEmbeddedSubst existsEmbeddedSubst liftTermSubst liftTerms)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalDirectTargetMapOriginTargets

theorem rowSubst {α β : Type} (code key row : OTerm α) (σ : α → OTerm β) :
    (originRow code key row).subst (fun a => emb (σ a)) =
      originRow (code.subst σ) (key.subst σ) (row.subst σ) := by
  simp only [originRow,conjunctionSubst,memberSubst,unarySubst,sucSubst,zSubst]

theorem rowRename {α β : Type} (code key row : OTerm α) (j : α → β) :
    (originRow code key row).relabel j =
      originRow (code.relabel j) (key.relabel j) (row.relabel j) := by
  simp only [originRow,conjunctionRename,graphRename,unaryRename,sucRelabel,zRelabel]

theorem originSubst {α β : Type} (code key : OTerm α) (σ : α → OTerm β) :
    (origin code key).subst (fun a => emb (σ a)) = origin (code.subst σ) (key.subst σ) := by
  simp only [origin,originBody,existsEmbeddedSubst,rowSubst,liftTermSubst] <;> rfl

theorem outputSubst {α β : Type} (code key out : OTerm α) (σ : α → OTerm β) :
    (atOutput code key out).subst (fun a => emb (σ a)) =
      atOutput (code.subst σ) (key.subst σ) (out.subst σ) := by
  simp only [atOutput,impSubst,conjunctionSubst,memberSubst,unarySubst,sucSubst,originSubst]

theorem allOutputsSubst {α β : Type} (code key : OTerm α) (σ : α → OTerm β) :
    (allOutputs code key).subst (fun a => emb (σ a)) =
      allOutputs (code.subst σ) (key.subst σ) := by
  simp only [allOutputs,allOutputsBody,allEmbeddedSubst,outputSubst,liftTermSubst] <;> rfl

private theorem originAsRename {α β : Type} (code key : OTerm α) (j : α → β) :
    (origin code key).relabel j = origin (code.relabel j) (key.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (origin code key).subst (fun a => emb (.var (j a))) = _
  simp only [originSubst, ← termRelabelAsSubst]

theorem originRename {α β : Type} (code key : OTerm α) (j : α → β) :
    (origin code key).relabel j = origin (code.relabel j) (key.relabel j) :=
  originAsRename code key j

theorem allOutputsRename {α β : Type} (code key : OTerm α) (j : α → β) :
    (allOutputs code key).relabel j = allOutputs (code.relabel j) (key.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (allOutputs code key).subst (fun a => emb (.var (j a))) = _
  simp only [allOutputsSubst, ← termRelabelAsSubst]

theorem instantiateRow {α : Type} (code key row : OTerm α) :
    instantiate (originBody code key) (emb row) = originRow code key row := by
  rw [originBody,instantiate,bindEmbedding,rowSubst]
  simp only [liftBind,varBind]

theorem instantiateOutput {α : Type} (code key out : OTerm α) :
    instantiate (allOutputsBody code key) (emb out) = atOutput code key out := by
  rw [allOutputsBody,instantiate,bindEmbedding,outputSubst]
  simp only [liftBind,varBind]

theorem motiveCode {α : Type} (code key : OTerm α) :
    atCode (motive key) code = allOutputs code key := by
  rw [atCode,instantiate,bindEmbedding]
  change (allOutputs (.var (.inr 0)) (key.relabel Sum.inl)).subst _ = _
  rw [allOutputsSubst,liftBind,varBind]

theorem motiveIndex {α : Type} (key : OTerm α) (i : Fin 3) :
    atIndex (motive key) i = allOutputs (.var (.inr i)) (key.relabel Sum.inl) := by
  unfold atIndex
  change (allOutputs (.var (.inr 0)) (key.relabel Sum.inl)).relabel _ = _
  rw [allOutputsRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginSyntaxProof
