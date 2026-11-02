module
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodePrimitiveProof
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodeSemanticProof
public import LogicLineages.OrdinalComparison.UnitEliminationTreeCodeProof
public import LogicLineages.OrdinalComparison.SourceUnitEliminationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode.Proof

theorem actualUniformSourceCompiler : Targets.ActualUniformSourceCompiler := by
  have hc : Computable₂ realizedCompileCode := Computable.option_map
    primitiveRecursiveSymbolicCompiler.2.to_comp
    (UnitEliminationTreeCode.Proof.exactAnchorRealization.1.comp Computable.snd).to₂
  refine ⟨hc,?_⟩
  intro Γ τ t
  obtain ⟨q,hq,hground,he⟩ := UnitElimination.Proof.fullSourceUnitElimination.2.2 Γ τ t
  have hcompile : compileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) =
      some (UnitEliminationTreeCode.code q) := by
    rw [compileCode,List.length_map,exactFuelBuild,hq]
    rfl
  refine ⟨q,hq,hcompile,?_,hground,he⟩
  rw [realizedCompileCode,hcompile,Option.map_some,
    UnitEliminationTreeCode.Proof.exactAnchorRealization.2 Γ q]
end LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode.Proof
