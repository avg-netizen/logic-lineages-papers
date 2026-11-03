module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerEffectivityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerCompiler.Proof
open CommonLayerSyntax

theorem sourceCodeSupport:Targets.SourceCodeSupport:=by
  intro Γ E F desired i hi
  unfold CommonLayerComparison.compileCode at hi
  rw [(BaseFormula.Proof.literalBaseFormulaCode _).2] at hi
  have hs:=CommonLayerComparison.Proof.originalSupport (headCodes Γ)
    (encodeCommon Γ.length E) (encodeCommon Γ.length F) desired i hi
  have hl:(headCodes Γ).length=Γ.length:=
    List.length_map (fun rho:NONote=>rawNoteEncode rho.1)
  have hE:CommonLayerComparison.codedVariables (headCodes Γ).length (encodeCommon Γ.length E)=
      commonVariables Γ.length E:=by
    unfold CommonLayerComparison.codedVariables
    rw [hl,CommonLayerSyntax.Proof.commonRoundtrip Γ.length E]
  have hF:CommonLayerComparison.codedVariables (headCodes Γ).length (encodeCommon Γ.length F)=
      commonVariables Γ.length F:=by
    unfold CommonLayerComparison.codedVariables
    rw [hl,CommonLayerSyntax.Proof.commonRoundtrip Γ.length F]
  rwa [hE,hF] at hs

theorem literalOutputs:Targets.LiteralOutputs:=by
  intro Γ E F desired
  exact ⟨CommonLayerComparison.compile Γ E F desired,rfl⟩

theorem completeCompiler:Targets.CompleteLayerCompiler:=
  ⟨CommonLayerComparison.Proof.codedComparison,CommonLayerComparison.Proof.actualComparison,
    CommonLayerComparison.Proof.originalSupport,CommonLayerComparison.Proof.allCodeEffectivity,
    sourceCodeSupport,literalOutputs⟩
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerCompiler.Proof
