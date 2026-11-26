module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeBranchProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
open PlainBlockDispatchCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

attribute [local irreducible] branches

theorem advance_computable : Computable advance := by
  have he : Computable (fun p : List StateData × StateData =>
      if p.2.1 = [] then [p.2] else branches p.2.1 p.2.2) :=
    ite_program (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
      (Computable.list_cons.comp Computable.snd (Computable.const []))
      (branches_computable.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
  exact flatMap_program ([], 0) Computable.id he.to₂
#print axioms advance_computable

attribute [local irreducible] advance

theorem run_computable : Computable₂ run := by
  have hs : Computable₂ (fun (_ : Nat × List StateData) => fun s : Nat × List StateData => advance s.2) :=
    advance_computable.comp (Computable.snd.comp Computable.snd)
  apply (Computable.nat_rec Computable.fst Computable.snd hs).of_eq
  intro p
  induction p.1 with
  | zero => rfl
  | succ n ih =>
      change advance (Nat.rec (motive := fun _ => List StateData) p.2 (fun _ s => advance s) n) = _
      rw [ih]
      exact (Function.iterate_succ_apply' advance n p.2).symm
#print axioms run_computable

theorem actualDispatchPrograms : PlainBlockDispatchCodeTargets.ActualDispatchPrograms := ⟨renameItem_primitive.to_comp, renameRow_primitive.to_comp, rename_computable,
    small_computable, ties_computable, bands_computable, far_computable,
    branches_computable, advance_computable, run_computable⟩
#print axioms actualDispatchPrograms

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
