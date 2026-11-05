module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupCodeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsRecursionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsProof
open PlainBranchSplitPrograms
attribute [local irreducible] Nat.sqrt Nat.unpair
attribute [local irreducible] MaximalPlainBranchPrograms.Code.variables
  MaximalPlainBranchPrograms.Code.cutoff MaximalPlainBranchPrograms.Code.eliminate
  PlainLinearCleanup.Code.cleanup BoundedRows.Code.block ZeroValuation.Code.evaluate

theorem small_primitive : Primrec Code.small := by
  have hp : Primrec₂ (fun code i : Nat => (i, MaximalPlainBranchPrograms.Code.cutoff code)) :=
    Primrec.snd.pair (MaximalPlainBranchProgramsProof.cutoff_primitive.comp Primrec.fst)
  have hm := Primrec.list_map MaximalPlainBranchProgramsProof.variables_primitive hp
  exact BoundedRowsCodeProof.block_primitive.comp hm Primrec.id

attribute [local irreducible] Code.small

theorem smallAnswer_primitive : Primrec Code.smallAnswer :=
  ZeroValuationProof.evaluate_primitive.comp small_primitive

theorem branches_primitive : Primrec Code.branches := by
  have hp : Primrec₂ (fun code i : Nat => MaximalPlainBranchPrograms.Code.eliminate i code) :=
    MaximalPlainBranchProgramsProof.eliminate_primitive.comp Primrec.snd Primrec.fst
  exact Primrec.list_map MaximalPlainBranchProgramsProof.variables_primitive hp

attribute [local irreducible] Code.smallAnswer Code.branches

theorem step_primitive : Primrec Code.step :=
  (smallAnswer_primitive.comp PlainLinearCleanupProof.cleanup_primitive).pair
    (branches_primitive.comp PlainLinearCleanupProof.cleanup_primitive)

theorem actualNumericPrograms : PlainBranchSplitProgramsTargets.ActualNumericPrograms :=
  ⟨small_primitive, smallAnswer_primitive, branches_primitive, step_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsProof
