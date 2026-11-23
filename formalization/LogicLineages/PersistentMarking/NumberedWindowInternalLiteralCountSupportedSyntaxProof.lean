module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (eqn emb bindEmbedding liftBind varBind sucRelabel zRelabel sucSubst zSubst eqnRelabel eqnSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalLiteralCountSupportedTargets

theorem acceptedRename {α β : Type} (code left right : OTerm α) (j : α → β) :
    (accepted code left right).relabel j = accepted (code.relabel j) (left.relabel j) (right.relabel j) := by
  simp only [accepted,programRename,tripleInputsRename,sucRelabel,zRelabel]

theorem countedRename {α β : Type} (list needle result : OTerm α) (j : α → β) :
    (counted list needle result).relabel j =
      counted (list.relabel j) (needle.relabel j) (result.relabel j) := by
  simp only [counted,programRename,binaryInputsRename]

theorem queryRename {α β : Type} (code left right needle lc rc : OTerm α) (j : α → β) :
    (query code left right needle lc rc).relabel j =
      query (code.relabel j) (left.relabel j) (right.relabel j) (needle.relabel j)
        (lc.relabel j) (rc.relabel j) := by
  change ((prem code left right needle lc rc).relabel j).imp ((eqn lc rc).relabel j) = _
  simp only [prem,query,conjunctionRename,acceptedRename,countedRename,graphRename,eqnRelabel]

private theorem acceptedSubst {α β : Type} (code left right : OTerm α) (σ : α → OTerm β) :
    (accepted code left right).subst (fun a => emb (σ a)) =
      accepted (code.subst σ) (left.subst σ) (right.subst σ) := by
  have tape : (fun i : Fin 3 => ((![code,left,right] : Fin 3 → OTerm α) i).subst σ) =
      ![code.subst σ,left.subst σ,right.subst σ] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  simp only [accepted,programSubst,tape,sucSubst,zSubst]

private theorem countedSubst {α β : Type} (list needle result : OTerm α) (σ : α → OTerm β) :
    (counted list needle result).subst (fun a => emb (σ a)) =
      counted (list.subst σ) (needle.subst σ) (result.subst σ) := by
  have tape : (fun i : Fin 2 => ((![list,needle] : Fin 2 → OTerm α) i).subst σ) =
      ![list.subst σ,needle.subst σ] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  simp only [counted,programSubst,tape]

private theorem querySubst {α β : Type} (code left right needle lc rc : OTerm α) (σ : α → OTerm β) :
    (query code left right needle lc rc).subst (fun a => emb (σ a)) =
      query (code.subst σ) (left.subst σ) (right.subst σ) (needle.subst σ) (lc.subst σ) (rc.subst σ) := by
  simp only [query,prem,impSubst,conjunctionSubst,acceptedSubst,countedSubst,memberSubst,eqnSubst]

theorem motiveCode {α : Type} (code left right needle lc rc : OTerm α) :
    atCode (motive left right needle lc rc) code = query code left right needle lc rc := by
  rw [atCode,instantiate,bindEmbedding]
  unfold motive
  rw [querySubst]
  simp only [liftBind,varBind]

theorem motiveIndex {α : Type} (left right needle lc rc : OTerm α) (i : Fin 3) :
    atIndex (motive left right needle lc rc) i =
      query (.var (.inr i)) (left.relabel Sum.inl) (right.relabel Sum.inl) (needle.relabel Sum.inl)
        (lc.relabel Sum.inl) (rc.relabel Sum.inl) := by
  unfold atIndex motive
  rw [queryRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
