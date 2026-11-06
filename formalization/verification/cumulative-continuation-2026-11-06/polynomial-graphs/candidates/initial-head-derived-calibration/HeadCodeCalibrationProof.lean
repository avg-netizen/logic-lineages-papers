module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
import LogicLineages.OrdinalComparison.PeakWordProgramWordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof

theorem headCodeCalibration : Targets.HeadCodeCalibration := by
  intro o
  constructor
  · simp only [headCalls, PeakWordProgram.peak.2, encodePrincipalKernelWord,
      List.map_map, Function.comp_def, rawNormCodeCorrect]
  · simp only [headDegree, rawNormCodeCorrect]

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof
