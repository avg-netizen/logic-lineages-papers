module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineTerminationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineProof
open Machine

noncomputable def stateValue (D : Nat) (s : State) : Bool :=
  s.1 || s.2.any (fun w => fuelValue D w.1 w.2.1 w.2.2)

theorem step_value (D : Nat) (s : State) : stateValue D (step D s) = stateValue D s := by
  rcases s with ⟨flag,work⟩
  cases flag with
  | true => simp [step,stateValue]
  | false =>
      cases work with
      | nil => simp [step,stateValue]
      | cons query rest =>
          rcases query with ⟨fuel,floor,code⟩
          by_cases h : Code.names code = []
          · cases fuel <;> simp [step,stateValue,fuelValue,h]
          · cases fuel with
            | zero => simp [step,stateValue,fuelValue,h]
            | succ fuel =>
                simp [step,stateValue,fuelValue,h,List.any_append,List.any_map,Function.comp_def]

theorem iterate_value (D steps : Nat) (s : State) :
    stateValue D ((step D)^[steps] s) = stateValue D s := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply',step_value,ih]

theorem initial_value (D fuel floor code : Nat) :
    stateValue D (initial fuel floor code) = fuelValue D fuel floor code := by
  simp [stateValue,initial]

theorem stopped_value (D : Nat) (s : State) (h : (s.1 || s.2.isEmpty) = true) :
    stateValue D s = s.1 := by
  rcases s with ⟨flag,work⟩
  cases flag with
  | true => simp [stateValue]
  | false =>
      cases work with
      | nil => simp [stateValue]
      | cons query rest => simp at h

theorem exactFiniteDepth : MachineTargets.ExactFiniteDepth := by
  intro D fuel floor code
  have hstop := (exactLeastStopping D fuel floor code).1
  change (run D fuel floor code (leastSteps D fuel floor code)).1 = _
  have hv := stopped_value D (run D fuel floor code (leastSteps D fuel floor code)) hstop
  rw [← hv]
  change stateValue D ((step D)^[leastSteps D fuel floor code]
    (initial fuel floor code)) = _
  rw [iterate_value,initial_value]

#print axioms stateValue
#print axioms step_value
#print axioms iterate_value
#print axioms initial_value
#print axioms stopped_value
#print axioms exactFiniteDepth

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineProof
