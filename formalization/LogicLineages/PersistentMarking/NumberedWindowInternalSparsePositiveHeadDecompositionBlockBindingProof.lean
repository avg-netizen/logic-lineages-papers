module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalBinderTransportSyntaxProof (rename renameCast formulaRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (exsRename)
open ID1Completion.InternalFiniteBlocks (block)

/-- The same syntax-only finite-binding argument as the older
InternalOriginalObjectFiberCertifiedLiftSyntaxProof, without importing
its different compiler or selection package. -/
private theorem renameFiniteBind {L : Language} {α β : Type} (f : α → β) {k n : Nat}
    (phi : L.BoundedFormula (α ⊕ Fin n) k) :
    rename f (phi.relabel id) = (rename (Sum.map f id) phi).relabel id := by
  have ht (j : Nat) (t : L.Term ((α ⊕ Fin n) ⊕ Fin j)) :
      (t.relabel (BoundedFormula.relabelAux (id : α ⊕ Fin n → α ⊕ Fin n) j)).relabel (Sum.map f id) =
      (t.relabel (Sum.map (Sum.map f id) id)).relabel
        (BoundedFormula.relabelAux (id : β ⊕ Fin n → β ⊕ Fin n) j) := by
    rw [Term.relabel_relabel,Term.relabel_relabel]
    congr 1
    funext i
    rcases i with (a | x) | y <;> simp [BoundedFormula.relabelAux]
  induction phi with
  | falsum => rfl
  | equal t u => simp only [rename,BoundedFormula.relabel,BoundedFormula.mapTermRel,ht]
  | rel r ts => simp only [rename,BoundedFormula.relabel,BoundedFormula.mapTermRel,ht]
  | imp p q ihp ihq => exact congrArg₂ BoundedFormula.imp ihp ihq
  | all p ih =>
    change (rename f ((p.relabel id).castLE _)).all = _
    rw [renameCast,ih]
    rfl

theorem blockRename {α β : Type} {k : Nat}
    (phi : ID1Completion.InternalCalculus.Formula (α ⊕ Fin k)) (j : α → β) :
    (block phi).relabel j = block (phi.relabel (Sum.map j id)) := by
  rw [formulaRelabel]
  unfold block
  rw [exsRename,renameFiniteBind,← formulaRelabel]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof
