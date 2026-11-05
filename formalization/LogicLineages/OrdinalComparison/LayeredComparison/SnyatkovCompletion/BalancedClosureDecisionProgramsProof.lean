module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionCodeInterface
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionProof
open BalancedClosureDecision

attribute [local irreducible] Nat.sqrt Nat.unpair BalancedExactVariables.rawSupport
  BalancedRawCompiler.recursiveCode

theorem positiveCode_primitive : Primrec positiveCode := by
  have hv : Primrec (fun i : Nat => 4 * i + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.id) (Primrec.const 1)
  have ha : Primrec (fun i : Nat => ([(3, 0, 4 * i + 1)] : Code)) :=
    Primrec.list_cons.comp ((Primrec.const 3).pair ((Primrec.const 0).pair hv)) (Primrec.const [])
  exact CommonHeadCode.Program.conjoin_primitive.comp
    (Primrec.list_map Primrec.id (ha.comp Primrec.snd).to₂)

attribute [local irreducible] positiveCode

theorem existsCode_computable : Computable existsCode :=
  CommonHeadCode.Program.conjunction_primitive.to_comp.comp
    (positiveCode_primitive.to_comp.comp BalancedClosureDecisionSuppliers.supportProgram)
    BalancedClosureDecisionSuppliers.rawCompiler.2

theorem forallCode_computable : Computable forallCode :=
  CommonHeadCode.Program.disjunction_primitive.to_comp.comp
    (CommonHeadCode.Program.negative_primitive.to_comp.comp
      (positiveCode_primitive.to_comp.comp BalancedClosureDecisionSuppliers.supportProgram))
    BalancedClosureDecisionSuppliers.rawCompiler.2

theorem existsAnswer_computable : Computable existsAnswer :=
  BaseBooleanSourceProof.decideClosureExists_primitive.to_comp.comp existsCode_computable

theorem forallAnswer_computable : Computable forallAnswer :=
  BaseBooleanSourceProof.decideClosureForall_primitive.to_comp.comp forallCode_computable

theorem actualAllCodePrograms : BalancedClosureDecisionTargets.ActualAllCodePrograms :=
  ⟨positiveCode_primitive, existsCode_computable, forallCode_computable,
    existsAnswer_computable, forallAnswer_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionProof
