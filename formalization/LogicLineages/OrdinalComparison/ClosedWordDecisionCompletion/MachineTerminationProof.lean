module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineProof
open Machine

noncomputable def stateCost (D : Nat) (s : State) : Nat :=
  (s.2.map (fun w => treeSize D w.1 w.2.1 w.2.2)).sum

/-- Every query costs at least its own finite transition. -/
theorem treeSize_positive (D fuel floor code : Nat) : 0 < treeSize D fuel floor code := by
  cases fuel with
  | zero => simp [treeSize]
  | succ fuel =>
      by_cases h : Code.names code = [] <;> simp [treeSize,h]

/-- The concrete expansion removes exactly one node of the finite tree sum.
No formula validity, semantic decrease or compiler-correctness premise occurs. -/
theorem step_cost (D : Nat) (s : State) (hflag : s.1 = false) (hne : s.2 ≠ []) :
    stateCost D (step D s)+1 = stateCost D s := by
  rcases s with ⟨flag,work⟩
  change flag = false at hflag
  subst flag
  cases work with
  | nil => exact False.elim (hne rfl)
  | cons query rest =>
      rcases query with ⟨fuel,floor,code⟩
      by_cases h : Code.names code = []
      · cases fuel <;> simp [step,stateCost,treeSize,h,Nat.add_comm]
      · cases fuel with
        | zero => simp [step,stateCost,treeSize,h,Nat.add_comm]
        | succ fuel =>
            simp only [step,Bool.false_eq_true,if_false,h,Nat.succ_ne_zero,
              Nat.add_one_sub_one,stateCost,List.map_append,List.sum_append,
              List.map_map,Function.comp_def,List.map_cons,List.sum_cons,
              treeSize,if_false]
            omega

theorem state_terminates (D : Nat) (s : State) :
    ∃ steps : Nat, ((step D)^[steps] s).1 = true ∨ ((step D)^[steps] s).2 = [] := by
  have h : ∀ n : Nat, ∀ t : State, stateCost D t = n →
      ∃ steps : Nat, ((step D)^[steps] t).1 = true ∨ ((step D)^[steps] t).2 = [] := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t ht
        by_cases hflag : t.1 = true
        · exact ⟨0,Or.inl hflag⟩
        by_cases hempty : t.2 = []
        · exact ⟨0,Or.inr hempty⟩
        have hc := step_cost D t (Bool.eq_false_of_not_eq_true hflag) hempty
        have hlt : stateCost D (step D t) < n := by omega
        obtain ⟨steps,hsteps⟩ := ih _ hlt (step D t) rfl
        refine ⟨steps+1,?_⟩
        simpa only [Function.iterate_succ_apply] using hsteps
  exact h _ s rfl

theorem allInputTermination : MachineTargets.AllInputTermination := by
  intro D fuel floor code
  obtain ⟨steps,hsteps⟩ := state_terminates D (initial fuel floor code)
  refine ⟨steps,?_⟩
  rcases hsteps with hflag | hempty
  · simp [stopped,run,hflag]
  · simp [stopped,run,hempty]

theorem exactLeastStopping : MachineTargets.ExactLeastStopping := by
  intro D fuel floor code
  have ht := allInputTermination D fuel floor code
  have hf : leastSteps D fuel floor code = Nat.find ht := by
    simp [leastSteps,ht]
  rw [hf]
  refine ⟨Nat.find_spec ht,?_⟩
  intro n hn
  exact Bool.eq_false_of_not_eq_true (Nat.find_min ht hn)

#print axioms stateCost
#print axioms treeSize_positive
#print axioms step_cost
#print axioms state_terminates
#print axioms allInputTermination
#print axioms exactLeastStopping

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineProof
