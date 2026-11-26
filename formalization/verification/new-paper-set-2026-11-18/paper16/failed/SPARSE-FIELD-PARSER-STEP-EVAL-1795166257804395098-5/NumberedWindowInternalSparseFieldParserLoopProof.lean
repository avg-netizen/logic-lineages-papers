module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserLoopProof
open NumberedWindowFieldAlgorithm
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowInternalSparseFieldParserRawPairProof (decodedPair tailBound)

def Terminal : State → Prop
  | none => True
  | some (n,_) => n = 0

theorem terminalNone : Terminal none := trivial

theorem terminalStep {s : State} (hs : Terminal s) : step s = s := by
  rcases s with _ | ⟨n,acc⟩
  · rfl
  change n = 0 at hs
  subst n
  rfl

theorem terminalSteps {s : State} (hs : Terminal s) (fuel : Nat) : steps fuel s = s := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [steps, terminalStep hs, ih]

theorem stepsAdd (base extra : Nat) (s : State) :
    steps (base+extra) s = steps extra (steps base s) := by
  induction base generalizing s with
  | zero => simp [steps]
  | succ base ih =>
    rw [Nat.succ_add, steps, steps, ih]

theorem reachesTerminal (n fuel : Nat) (acc : List Nat) (hle : n ≤ fuel) :
    Terminal (steps fuel (some (n,acc))) := by
  induction n using Nat.strongRecOn generalizing fuel acc with
  | ind n ih =>
    cases n with
    | zero =>
      have terminal : Terminal (some (0,acc)) := rfl
      rw [terminalSteps terminal]
      exact terminal
    | succ n =>
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero n hle)
      | succ fuel =>
        rw [steps, step]
        cases found : decode n with
        | none =>
          change Terminal (steps fuel none)
          rw [terminalSteps (s := none) trivial]
          exact trivial
        | some ht =>
          obtain ⟨h,t⟩ := ht
          change Terminal (steps fuel (some (t,h::acc)))
          have htn := tailBound h t
          rw [decodedPair found] at htn
          exact ih t (Nat.lt_succ_of_le htn) fuel (h::acc)
            (Nat.le_trans htn (Nat.le_of_succ_le_succ hle))

def extend (acc : List Nat) : State → State
  | none => none
  | some (n,prior) => some (n,prior ++ acc)

theorem stepExtend (extra : List Nat) (s : State) :
    step (extend extra s) = extend extra (step s) := by
  rcases s with _ | ⟨n,acc⟩
  · rfl
  cases n with
  | zero => rfl
  | succ n =>
    simp only [extend,step]
    cases decode n with
    | none => rfl
    | some ht => obtain ⟨h,t⟩ := ht; rfl

theorem stepsExtend (extra : List Nat) (fuel : Nat) (s : State) :
    steps fuel (extend extra s) = extend extra (steps fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => rw [steps, stepExtend, ih, steps]

theorem finishExtend (extra : List Nat) (s : State) :
    finish (extend extra s) = (finish s).map (fun xs => extra.reverse ++ xs) := by
  rcases s with _ | ⟨n,acc⟩
  · rfl
  by_cases eq : n = 0 <;> simp [finish,extend,eq,List.reverse_append]

theorem enough (n fuel : Nat) (acc : List Nat) (hle : n ≤ fuel) :
    finish (steps fuel (some (n,acc))) = (unpack n).map (fun xs => acc.reverse ++ xs) := by
  have hp : n+(fuel-n) = fuel := Nat.add_sub_of_le hle
  rw [← hp, stepsAdd, terminalSteps (reachesTerminal n n acc (Nat.le_refl n))]
  change finish (steps n (extend acc (some (n,[])))) = _
  rw [stepsExtend, finishExtend, unpack]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserLoopProof
