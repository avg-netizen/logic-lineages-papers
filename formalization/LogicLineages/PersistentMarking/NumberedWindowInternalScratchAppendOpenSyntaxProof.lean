module

public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding liftBind varBind sucRelabel zRelabel sucSubst zSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalScratchAppendOpenTargets

theorem appendRename {α β : Type} (out raw suffix : OTerm α) (j : α → β) :
    (appendGraph out raw suffix).relabel j =
      appendGraph (out.relabel j) (raw.relabel j) (suffix.relabel j) := by
  simp only [appendGraph,programRename,binaryInputsRename]

theorem testedRename {α β : Type} (raw suffix k : OTerm α) (j : α → β) :
    (tested raw suffix k).relabel j = tested (raw.relabel j) (suffix.relabel j) (k.relabel j) := by
  simp only [tested,programRename,tripleInputsRename,sucRelabel,zRelabel]

theorem appearsRename {α β : Type} (raw suffix k : OTerm α) (j : α → β) :
    (appears raw suffix k).relabel j = appears (raw.relabel j) (suffix.relabel j) (k.relabel j) := by
  change ((memberGraph raw k).relabel j ⊔ (memberGraph suffix k).relabel j) = _
  simp only [graphRename]

theorem atListRename {α β : Type} (raw suffix k : OTerm α) (j : α → β) :
    (atList raw suffix k).relabel j = atList (raw.relabel j) (suffix.relabel j) (k.relabel j) := by
  change ((appears raw suffix k).relabel j).imp ((tested raw suffix k).relabel j) = _
  rw [appearsRename,testedRename]

private theorem testedSubst {α β : Type} (raw suffix k : OTerm α) (ts : α → OTerm β) :
    (tested raw suffix k).subst (fun a => emb (ts a)) =
      tested (raw.subst ts) (suffix.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![raw,suffix,k] : Fin 3 → OTerm α) i).subst ts) =
      ![raw.subst ts,suffix.subst ts,k.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  unfold tested
  rw [programSubst,tape,sucSubst,zSubst]

private theorem appearsSubst {α β : Type} (raw suffix k : OTerm α) (ts : α → OTerm β) :
    (appears raw suffix k).subst (fun a => emb (ts a)) =
      appears (raw.subst ts) (suffix.subst ts) (k.subst ts) := by
  change ((memberGraph raw k).subst (fun a => emb (ts a)) ⊔
    (memberGraph suffix k).subst (fun a => emb (ts a))) = _
  simp only [memberSubst]

private theorem atListSubst {α β : Type} (raw suffix k : OTerm α) (ts : α → OTerm β) :
    (atList raw suffix k).subst (fun a => emb (ts a)) =
      atList (raw.subst ts) (suffix.subst ts) (k.subst ts) := by
  simp only [atList,impSubst,appearsSubst,testedSubst]

theorem atCodeEq {α : Type} (raw suffix k : OTerm α) :
    atCode (motive suffix k) raw = atList raw suffix k := by
  rw [atCode,instantiate,bindEmbedding]
  change (atList (.var (.inr 0)) (suffix.relabel Sum.inl) (k.relabel Sum.inl)).subst _ = _
  rw [atListSubst]
  simp only [liftBind,varBind]

theorem atIndexEq {α : Type} (suffix k : OTerm α) (i : Fin 3) :
    atIndex (motive suffix k) i =
      atList (.var (.inr i)) (suffix.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex
  change (atList (.var (.inr 0)) (suffix.relabel Sum.inl) (k.relabel Sum.inl)).relabel _ = _
  rw [atListRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
