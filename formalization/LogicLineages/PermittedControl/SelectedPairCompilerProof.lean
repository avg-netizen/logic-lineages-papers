module
public import LogicLineages.PermittedControl.SelectedPairCompilerAlgebraProof
public import LogicLineages.OrdinalComparison.SourceSignedPairAdapterProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PlainSystemCodeCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeProgramsProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPairCompiler.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SignedPair

theorem semanticCompiler : SelectedPairCompilerTargets.SemanticCompiler := by
  intro n d
  refine ⟨(SignedPair.Proof.compiler_bound d).1, (SignedPair.Proof.compiler_bound d).2, ?_⟩
  intro ctrl B hc pol ρ
  obtain ⟨v, hv, h0, h1, hp0, hp1, he, hn⟩ :=
    SelectedHardnessCoordinatesProof.coordinateFacts ctrl B hc _ pol ρ (compile d).pair.1
  obtain ⟨w, hw, h0', h1', hp0', hp1', he', hn'⟩ :=
    SelectedHardnessCoordinatesProof.coordinateFacts ctrl B hc _ pol ρ (compile d).pair.2
  exact ⟨hp1, hp1', compiler_difference ctrl B hc pol d ρ⟩

theorem fullSelectedPairCompiler : SelectedPairCompilerTargets.FullSelectedPairCompiler :=
  ⟨semanticCompiler, SignedPair.Proof.monomialAdapter,
    FunctionalHardnessCompletion.PlainSystemCode.Proof.exactPlainCompiler,
    FunctionalHardnessCompletion.SeededSourceCode.Proof.compiler_pr⟩
end LogicLineages.PermittedControl.SelectedPairCompiler.Proof
