module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeLowerProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
open TiedLinearCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem actualAdapterPrograms : TiedLinearCodeTargets.ActualAdapterPrograms :=
  ⟨tokens_primitive.to_comp, liftFormula_computable, lowerFormula_computable⟩
#print axioms actualAdapterPrograms

attribute [local irreducible] liftFormula lowerFormula tokens

theorem actualEliminationProgram : TiedLinearCodeTargets.ActualEliminationProgram := by
  change Computable (fun p : Nat × Nat => eliminate p.1 p.2)
  unfold eliminate
  have ht : Computable (fun p : Nat × Nat => tokens p.2) := tokens_primitive.to_comp.comp Computable.snd
  have hl : Computable (fun p : Nat × Nat => liftFormula (tokens p.2) p.1 p.2) :=
    liftFormula_computable.comp (ht.pair (Computable.fst.pair Computable.snd))
  have he : Computable (fun p : Nat × Nat => LinearRows.Code.eliminate 0 (liftFormula (tokens p.2) p.1 p.2)) :=
    LinearRowsCodeProof.eliminate_primitive.to_comp.comp (Computable.const 0) hl
  exact lowerFormula_computable.comp (ht.pair (Computable.fst.pair he))
#print axioms actualEliminationProgram

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
