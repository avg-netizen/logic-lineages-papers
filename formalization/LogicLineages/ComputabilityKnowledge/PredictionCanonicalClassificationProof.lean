module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalClassificationTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpperProof
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardnessProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalClassificationProof
open PredictionCanonicalClassification PredictionCanonicalClassificationTargets

theorem wholeSourceCanonicalTheorem : WholeSourceCanonicalTheorem := by
  refine ⟨?_,PredictionCanonicalHardnessProof.canonicalFixedThresholds,?_,
    PredictionCanonicalHardnessProof.actualCanonicalMeasureLower⟩
  · intro p hp
    exact PredictionSourceFiniteValuesProof.wholeSourceFiniteValues _
      PredictionCanonicalTapeBoundsProof.exactCanonicalCoverage.1 p hp
  · obtain ⟨u,v,hr,hs⟩ := PredictionCanonicalMeasureUpperProof.canonicalFiniteUpper
    refine ⟨PredictionCanonicalMeasureUpper.result u v,hr,?_⟩
    intro p hp
    obtain ⟨h,heval,hheight⟩ := hs p hp
    refine ⟨h+1,heval,?_⟩
    change PredictionOriginalMeasureAlgorithm.outputValue (h+1) =
      PredictionCanonicalTapeBounds.height (PredictionTapeObservation.policy p hp)
    simpa [PredictionOriginalMeasureAlgorithm.outputValue] using hheight.symm

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalClassificationProof
