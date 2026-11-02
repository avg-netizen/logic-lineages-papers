module
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodeSemanticProof
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodePrimitiveProof
public import LogicLineages.OrdinalComparison.NumericUnaryChainProof
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListProof
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode.Proof
open HeterogeneousUnaryAssembly OriginalScaleFlatList NumericUnaryChain

theorem actualScaledCompiler : Targets.ActualScaledCompiler := by
  intro k Γ xs C b c hb hc
  obtain ⟨uC,vC,hC,hSat,hCval,K,hK,hgap,hbal⟩ :=
    OriginalScaleFlatList.Proof.actualOriginalScaleChain k Γ xs C b c hb hc
  let caller := unaryInput Γ (UnaryCarrier.saturate k C) vC hSat
  let inputs := paidList b xs caller
  have he : DeterministicCarrierData.saturateVector k uC = vC :=
    Option.some.inj ((DeterministicCarrierData.Proof.exactSaturation Γ k C uC hC).1.symm.trans hSat)
  have hcaller : callerCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode (Ty.curriedGround (k+1)))
      (SyntaxCode.encodeTerm C) = some (operatorCode caller) := by
    rw [exactCallerCode k Γ C uC hC,he]
    rfl
  have hp := exactPaidList Γ b xs caller c
  have hcompile : compileScaleCode (Γ.map SyntaxCode.typeCode)
      (SyntaxCode.typeCode (Ty.curriedGround (k+1))) (SyntaxCode.encodeTerm C) b (xs.map operatorCode) =
      some ((context inputs).map SyntaxCode.typeCode,
        SyntaxCode.encodeTerm (SourceUnaryChain.chainSource (terms inputs)),OrdinalSyntax.vectorCode K) := by
    unfold compileScaleCode
    rw [hcaller]
    change NumericUnaryChain.compileCode (Γ.map SyntaxCode.typeCode) (paidCode b (xs.map operatorCode) (operatorCode caller)) = _
    rw [hp.1]
    obtain ⟨K',hcode,hassign,hvalue⟩ := NumericUnaryChain.Proof.actualCompiledChain Γ inputs
    have hEq : K' = K := Option.some.inj (hassign.symm.trans hK)
    subst K'
    exact hcode
  refine ⟨uC,vC,hC,hSat,hCval,K,hcompile,hK,?_,?_⟩
  · rw [hp.2]
    exact hgap
  · rw [hp.2]
    exact hbal
end LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode.Proof
