module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeFormulaProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
open PlainBlockProjectionCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem any_primitive : Primrec WindowCode.any := Primrec.list_foldr Primrec.id (Primrec.const 1)
  ((PlainBlockLinearizationCodeProof.binary_primitive 8 7).comp
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
#print axioms any_primitive

theorem readout_primitive : Primrec readout := any_primitive.comp (Primrec.list_map Primrec.id
  (formula_primitive.comp (Primrec.snd.comp Primrec.snd)).to₂)
#print axioms readout_primitive

attribute [local irreducible] readout PlainBlockDispatchCode.run

theorem project_computable : Computable₂ project := by
  have hi : Computable (fun p : List Nat × Nat => [p]) :=
    Computable.list_cons.comp Computable.id (Computable.const [])
  exact readout_primitive.to_comp.comp
    (PlainBlockDispatchCodeProof.run_computable.comp (Computable.list_length.comp Computable.fst) hi)
#print axioms project_computable

theorem actualProjectionPrograms : PlainBlockProjectionCodeTargets.ActualProjectionPrograms := ⟨positiveTerm_primitive.to_comp, negativeTerm_primitive.to_comp, absoluteTerm_primitive.to_comp,
    atom_primitive.to_comp, formula_primitive.to_comp, readout_primitive.to_comp, project_computable⟩
#print axioms actualProjectionPrograms

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
