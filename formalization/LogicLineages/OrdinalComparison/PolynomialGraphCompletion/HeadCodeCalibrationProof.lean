module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
import LogicLineages.OrdinalComparison.PeakWordProgramWordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof

theorem headCodeCalibration : Targets.HeadCodeCalibration := by
  intro o
  constructor
  · simp only [headCalls, PeakWordProgram.peak.2, encodePrincipalKernelWord,
      List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    rw [rawNormCodeCorrect p.1]
  · unfold headDegree
    rw [rawNormCodeCorrect o]

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof
