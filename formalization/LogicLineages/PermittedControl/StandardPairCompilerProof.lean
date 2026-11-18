module
public import LogicLineages.PermittedControl.StandardPairCompilerAlgebraProof
public import LogicLineages.OrdinalComparison.SourceSignedPairAdapterProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PlainSystemCodeCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeProgramsProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardPairCompiler.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SignedPair

theorem semanticCompiler : SemanticCompiler := by
  intro n d
  refine ⟨(SignedPair.Proof.compiler_bound d).1,(SignedPair.Proof.compiler_bound d).2,?_⟩
  intro pol ρ
  exact ⟨StandardSourceFacts.Proof.unaryFacts _ pol ρ _,
    StandardSourceFacts.Proof.unaryFacts _ pol ρ _,compiler_difference pol d ρ⟩

theorem standardPairCompiler : StandardPairCompiler :=
  ⟨semanticCompiler,SignedPair.Proof.monomialAdapter,
    FunctionalHardnessCompletion.PlainSystemCode.Proof.exactPlainCompiler,
    FunctionalHardnessCompletion.SeededSourceCode.Proof.compiler_pr⟩
end LogicLineages.PermittedControl.StandardPairCompiler.Proof
