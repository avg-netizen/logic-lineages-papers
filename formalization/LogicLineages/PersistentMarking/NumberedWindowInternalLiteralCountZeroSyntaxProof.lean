module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind zRelabel zSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (notSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (countedRename)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountZeroTargets

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

theorem zeroRename {α β : Type} (code needle : OTerm α) (j : α → β) :
    (zeroAt code needle).relabel j = zeroAt (code.relabel j) (needle.relabel j) := by
  simp only [zeroAt,impRename,notRename,graphRename,countedRename,zRelabel]

private theorem zeroSubst {α β : Type} (code needle : OTerm α) (σ : α → OTerm β) :
    (zeroAt code needle).subst (fun a => emb (σ a)) =
      zeroAt (code.subst σ) (needle.subst σ) := by
  simp only [zeroAt,impSubst,notSubst,memberSubst,countedSubst,zSubst]

theorem zeroCode {α : Type} (code needle : OTerm α) :
    atCode (zeroMotive needle) code = zeroAt code needle := by
  rw [atCode,instantiate,bindEmbedding]
  unfold zeroMotive
  rw [zeroSubst]
  simp only [liftBind,varBind]

theorem zeroIndex {α : Type} (needle : OTerm α) (i : Fin 3) :
    atIndex (zeroMotive needle) i = zeroAt (.var (.inr i)) (needle.relabel Sum.inl) := by
  unfold atIndex zeroMotive
  rw [zeroRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroSyntaxProof
