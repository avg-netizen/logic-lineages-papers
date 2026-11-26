module
public import LogicLineages.StandardControlCurrent.GraphNetwork.AllocationProof
public import LogicLineages.StandardControlCurrent.GraphNetwork.BlockProof
public import LogicLineages.StandardControlCurrent.GraphNetwork.CalibrationProof
public import LogicLineages.StandardControlCurrent.GraphNetwork.SemanticProof
public import LogicLineages.StandardControlCurrent.GraphNetwork.ProgramsProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineCorrectnessProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetwork.Proof
open OrdinalComparison WordLinearDecisionCompletion

 theorem decision : Targets.NetworkDecision := by
  intro d hs bs rs p hv
  have hd := SemanticProof.full d hs bs rs p hv
  have he := ClosedWordDecisionCompletion.MachineProof.actualClosedDecision
    (degree hs bs) (matrix d hs bs rs p) hd.2.1
  have hc := CalibrationProof.full.2 d hs bs rs p
  simp only [Code.decide,hc]
  rw [he]
  constructor
  · rintro ⟨ν,_,hν⟩
    exact ⟨ν,(hd.2.2.2 ν).mp hν⟩
  · rintro ⟨ν,hν⟩
    exact ⟨ν,hd.2.2.1 ν,(hd.2.2.2 ν).mpr hν⟩

 theorem full : Targets.FullGraphDomains :=
  ⟨CalibrationProof.full,ProgramsProof.full,AllocationProof.full,BlockProof.full,
    SemanticProof.full,decision⟩
end LogicLineages.StandardControlCurrent.GraphNetwork.Proof
