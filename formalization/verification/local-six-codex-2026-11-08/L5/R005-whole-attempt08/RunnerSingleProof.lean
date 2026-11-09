module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerStepProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerTerminationProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerFamilyProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm Runner

/-- The actual least-stopping run empties its pending stack. The source
package follows from its maintained invariant, including false branch domains. -/
theorem exactSingleRowPackage : RunnerTargets.ExactSingleRowPackage := by
  intro D maximum r hDegree hrow
  have ha : admitted D r = true := (admitted_correct D r).mpr ⟨hDegree,hrow⟩
  have hstop := (exactLeastStopping D maximum r).1
  have hempty : (run D maximum r (leastFuel D maximum r)).work = [] := by
    cases hw : (run D maximum r (leastFuel D maximum r)).work with
    | nil => rfl
    | cons w ws => simp [stopped,ha,hw] at hstop
  have hi := run_invariant D maximum hDegree r hrow (leastFuel D maximum r)
  simpa only [solve,ha,if_true] using
    finish_invariant_correct D maximum r (run D maximum r (leastFuel D maximum r)) hi hempty

theorem exactFamilyPackage : RunnerTargets.ExactFamilyPackage :=
  familyPackage_of_single exactSingleRowPackage

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerProof
