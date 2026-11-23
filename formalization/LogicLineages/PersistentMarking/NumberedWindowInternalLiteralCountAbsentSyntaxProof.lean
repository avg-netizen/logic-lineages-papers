module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding liftBind varBind eqnRelabel eqnSubst zRelabel zSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (notSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open NumberedWindowInternalLiteralCount (entryCount)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (countedRename)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountAbsentTargets

private theorem countedSubst {α β : Type} (list needle result : OTerm α) (σ : α → OTerm β) :
    (counted list needle result).subst (fun a => emb (σ a)) =
      counted (list.subst σ) (needle.subst σ) (result.subst σ) := by
  have tape : (fun i : Fin 2 => ((![list,needle] : Fin 2 → OTerm α) i).subst σ) =
      ![list.subst σ,needle.subst σ] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  simp only [counted,programSubst,tape]

private theorem notRename {α β : Type} (p : Formula α) (j : α → β) :
    p.not.relabel j = (p.relabel j).not := rfl

theorem absentRename {α β : Type} (code needle out : OTerm α) (j : α → β) :
    (absentAt code needle out).relabel j = absentAt (code.relabel j) (needle.relabel j) (out.relabel j) := by
  simp only [absentAt,impRename,conjunctionRename,notRename,graphRename,countedRename,eqnRelabel,zRelabel]

theorem absentSubst {α β : Type} (code needle out : OTerm α) (σ : α → OTerm β) :
    (absentAt code needle out).subst (fun a => emb (σ a)) =
      absentAt (code.subst σ) (needle.subst σ) (out.subst σ) := by
  simp only [absentAt,impSubst,conjunctionSubst,notSubst,memberSubst,countedSubst,eqnSubst,zSubst]

theorem absentCode {α : Type} (code needle out : OTerm α) :
    atCode (absentMotive needle out) code = absentAt code needle out := by
  rw [atCode,instantiate,bindEmbedding]
  unfold absentMotive
  rw [absentSubst]
  simp only [liftBind,varBind]

theorem absentIndex {α : Type} (needle out : OTerm α) (i : Fin 3) :
    atIndex (absentMotive needle out) i =
      absentAt (.var (.inr i)) (needle.relabel Sum.inl) (out.relabel Sum.inl) := by
  unfold atIndex absentMotive
  rw [absentRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentSyntaxProof
