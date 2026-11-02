module
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeComputableProof
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeSyntaxProof
public import LogicLineages.OrdinalComparison.ActualHeadGraphFormulaProof
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeProof
public import LogicLineages.OrdinalComparison.ContextInsertionCodeProof
public import LogicLineages.OrdinalComparison.UnitHeadCodeProof
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodeProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Proof
open ForwardTranslation Arithmetic ArithmeticCode FormulaConstruction
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem ray_source_exact (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1)) :
    raySourceCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) =
      SyntaxCode.encodeTerm (ActualUnaryRay.source K) := by
  have hc : GroundCaptureClosingCode.sourceCode (Γ.map SyntaxCode.typeCode) 0 (SyntaxCode.encodeTerm K) =
      SyntaxCode.encodeTerm (UnaryCarrier.closeGround K) :=
    GroundCaptureClosingCode.Proof.exactProtectedSource [] Γ _ K
  have hi := ContextInsertionCode.Proof.exactSourceInsertion [] [.ground] Γ _ (UnaryCarrier.closeGround K)
  change ContextInsertionCode.sourceCode 0 1 (SyntaxCode.encodeTerm (UnaryCarrier.closeGround K)) = _ at hi
  rw [raySourceCode,hc,hi]
  rfl

theorem actualEffectiveWholeGraph : Targets.ActualEffectiveWholeGraph := by
  intro Γ K
  obtain ⟨u,a,c,q,hconst,hbuild,hground,hsem⟩ := FormulaConstruction.Proof.actualWholeGenuineGraph Γ K
  have hs := ray_source_exact Γ K
  have ht := (SyntaxCode.Proof.typedCheckExact Γ (Ty.curriedGround 1) (SyntaxCode.encodeTerm K)).mpr ⟨K,rfl⟩
  have hv : DefaultSourceAssignment.assignmentCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) =
      some (OrdinalSyntax.vectorCode u) := by
    rw [DefaultSourceAssignment.Proof.assignmentCorrect,hconst.1]
    rfl
  have hget0 : (OrdinalSyntax.vectorCode u).getD 0 0 = OrdinalSyntax.typedCode (u 0) := by
    simp [OrdinalSyntax.vectorCode,List.getD_eq_getElem?_getD]
  have hget1 : (OrdinalSyntax.vectorCode u).getD 1 0 =
      OrdinalSyntax.typedCode (u (UnaryCarrier.headIndex 0)) := by
    simp [OrdinalSyntax.vectorCode,List.getD_eq_getElem?_getD,UnaryCarrier.headIndex,Ty.curriedGround,Ty.level]
    exact congrArg (fun j => OrdinalSyntax.typedCode (u j)) (Fin.ext rfl)
  have hp : UnitHeadCode.positiveCode ((OrdinalSyntax.vectorCode u).getD 1 0) = some (closedPositiveCode a) := by
    rw [hget1,(UnitHeadCode.Proof.exactRawUnitExtraction Γ _).2,hconst.2.1]
    rfl
  have hc : UnitScalarEvaluationCode.valueCode ((OrdinalSyntax.vectorCode u).getD 0 0) = some c := by
    rw [hget0]
    exact hconst.2.2
  have hr : UnitEliminationBuildCode.realizedCompileCode (0::Γ.map SyntaxCode.typeCode)
      (raySourceCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K)) =
        some (UnitEliminationTreeCode.code (UnitElimination.realize q)) := by
    rw [hs]
    change UnitEliminationBuildCode.realizedCompileCode ((.ground::Γ).map SyntaxCode.typeCode)
      (SyntaxCode.encodeTerm (ActualUnaryRay.source K)) = _
    rw [UnitEliminationBuildCode.realizedCompileCode,UnitEliminationBuildCode.compileCode,
      List.length_map,UnitEliminationBuildCode.Proof.exactFuelBuild,hbuild]
    simp only [Option.map_some]
    exact congrArg some (UnitEliminationTreeCode.Proof.exactAnchorRealization.2 (.ground::Γ) q)
  have hout : constantsCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) =
      some (closedPositiveCode a,c,UnitEliminationTreeCode.code (UnitElimination.realize q)) := by
    rw [constantsCode,ht]
    simp only [bind,pure,Option.bind_some,if_pos rfl]
    rw [hv]
    simp only [Option.bind_some]
    rw [hp]
    simp only [Option.bind_some]
    rw [hc]
    simp only [Option.bind_some]
    rw [hr]
    rfl
  refine ⟨u,a,c,q,hconst,hs,hbuild,hout,?_⟩
  intro δ t y
  refine ⟨?_,hsem δ t y⟩
  rw [compileCode,hout,Option.map_some,List.length_map,exactFormulaCompilation]
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Proof
