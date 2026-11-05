module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionCodeInterface
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaDataProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesProof
open CommonHeadExactVariables

/-- Only the finite equality padding is primitive recursive. -/
theorem padding_primitive : Primrec BalancedExactVariables.variablesCode := by
  have hv : Primrec (fun i : Nat => 4 * i + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.id) (Primrec.const 1)
  have he : Primrec (fun i : Nat => ([(2, 4 * i + 1, 4 * i + 1)] : Code)) :=
    Primrec.list_cons.comp ((Primrec.const 2).pair (hv.pair hv)) (Primrec.const [])
  exact CommonHeadCode.Program.conjoin_primitive.comp
    (Primrec.list_map Primrec.id (he.comp Primrec.snd).to₂)

attribute [local irreducible] Nat.sqrt Nat.unpair CommonLayerComparison.codedVariables

theorem support_computable : Computable (fun p : Input => support p.1 p.2.1 p.2.2.1) := by
  have hn : Computable (fun p : Input => p.1.length) := Primrec.list_length.to_comp.comp Computable.fst
  have he : Computable (fun p : Input => p.2.1) := Computable.fst.comp Computable.snd
  have hf : Computable (fun p : Input => p.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  exact BalancedBoxFormula.Program.dedup_primitive.to_comp.comp
    (Primrec.list_append.to_comp.comp
      (CommonHeadExactVariablesSupport.actualSupportProgram.comp hn he)
      (CommonHeadExactVariablesSupport.actualSupportProgram.comp hn hf))

theorem actualOutputProgram : CommonHeadExactVariablesTargets.ActualOutputProgram :=
  CommonHeadCode.Program.conjunction_primitive.to_comp.comp
    CommonHeadClosureDecisionSuppliers.allCodeEffectivity
    (padding_primitive.to_comp.comp support_computable)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesProof
