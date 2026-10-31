module
public import LogicLineages.ComputabilityKnowledge.PredictionSourceRobustTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSourceRobustProof
open PredictionSourceRobustTargets
open PredictionRobust (historyPrefix)

theorem sourceRobustBaseline : SourceRobustBaseline := by
  intro b _ e he htime y
  obtain ⟨N, hN⟩ := (PredictionTapeRuntimeClassProof.exactAvailabilityCalibration e he b).2 htime
  have ha : PredictionTapeBaseline.available e he b y :=
    ⟨N, fun n hn => hN n hn (historyPrefix y n) (by simp [historyPrefix])⟩
  exact PredictionTapeBaselineProof.robustBoundedObservations e he b y ha

end LogicLineages.ComputabilityKnowledge.PredictionSourceRobustProof
