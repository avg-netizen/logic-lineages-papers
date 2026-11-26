module
public import LogicLineages.StandardControlCurrent.PolicyPartialSyntaxProof
public import LogicLineages.StandardControlCurrent.PolicyPartialRunPrograms
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyPartialStatementChecks
theorem full : PolicyPartialTargets.Full :=
  ⟨PolicyPartialMergeProof.calibration, PolicyPartialSyntaxProof.literal,
    fun p hp => ⟨PolicyPartialMergePrograms.coordinate p hp,
      PolicyPartialMergePrograms.merge p hp,PolicyPartialRunPrograms.run p hp⟩⟩
#print axioms full
end LogicLineages.StandardControlCurrent.PolicyPartialStatementChecks
