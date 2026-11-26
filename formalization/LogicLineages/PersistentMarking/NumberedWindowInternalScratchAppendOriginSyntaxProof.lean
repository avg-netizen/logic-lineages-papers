module

public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginSyntaxProof
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
open NumberedWindowInternalScratchAppendOpenTargets (tested appears)
open NumberedWindowInternalScratchAppendOpenSyntaxProof (appearsRename testedRename)
open NumberedWindowInternalScratchAppendOriginTargets

theorem backAtRename {α β : Type} (raw suffix k : OTerm α) (j : α → β) :
    (backAt raw suffix k).relabel j = backAt (raw.relabel j) (suffix.relabel j) (k.relabel j) := by
  change ((tested raw suffix k).relabel j).imp ((appears raw suffix k).relabel j) = _
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

private theorem backAtSubst {α β : Type} (raw suffix k : OTerm α) (ts : α → OTerm β) :
    (backAt raw suffix k).subst (fun a => emb (ts a)) =
      backAt (raw.subst ts) (suffix.subst ts) (k.subst ts) := by
  simp only [backAt,impSubst,appearsSubst,testedSubst]

theorem atCodeEq {α : Type} (raw suffix k : OTerm α) :
    atCode (backMotive suffix k) raw = backAt raw suffix k := by
  rw [atCode,instantiate,bindEmbedding]
  change (backAt (.var (.inr 0)) (suffix.relabel Sum.inl) (k.relabel Sum.inl)).subst _ = _
  rw [backAtSubst]
  simp only [liftBind,varBind]

theorem atIndexEq {α : Type} (suffix k : OTerm α) (i : Fin 3) :
    atIndex (backMotive suffix k) i =
      backAt (.var (.inr i)) (suffix.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex
  change (backAt (.var (.inr 0)) (suffix.relabel Sum.inl) (k.relabel Sum.inl)).relabel _ = _
  rw [backAtRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginSyntaxProof
