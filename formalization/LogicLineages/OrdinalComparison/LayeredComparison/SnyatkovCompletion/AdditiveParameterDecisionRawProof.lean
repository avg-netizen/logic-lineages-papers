module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionCodeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecRoundtripProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionProof

theorem actualRawDecision : AdditiveParameterDecisionTargets.ActualRawDecision := by
  intro values code
  have h := literalCodeDecision values (SourceFormulaCodec.decode code)
  rw [SourceFormulaCodecProof.codeRoundtrip] at h
  rw [h]
  exact ⟨exactDecisionDomain values _, actualDecision values _⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionProof
