module
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodePrimitiveProof
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodeSemanticProof
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodeProof
public import LogicLineages.OrdinalComparison.ActualHeadGraphArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode.Proof
open Arithmetic ArithmeticCode

theorem actualSourceFormula : Targets.ActualSourceFormula := by
  intro Γ τ t xs r hlen
  obtain ⟨q,hq,hcompile,hreal,hground,he⟩ :=
    UnitEliminationBuildCode.Proof.actualUniformSourceCompiler.2 Γ τ t
  refine ⟨unitFormula (UnitElimination.realize q) xs r,?_,?_⟩
  · rw [sourceFormulaCode,hreal,Option.map_some,exactTreeExpansion]
  · intro ν
    exact (Arithmetic.Proof.unitTreeExpansion Γ (UnitElimination.realize q) xs hlen r ν).trans
      (he (inputValues ν xs) (r.value ν))
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode.Proof
