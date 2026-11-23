module

public import LogicLineages.NativeModule.PersistentMarking.InsertionTargets
public import LogicLineages.NativeModule.PersistentMarking.SubstitutionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.InsertionProof
open Spine

theorem getNoneLength (values : Args) (n : Nat) (h : values.get n = none) :
    values.length ≤ n := by
  cases values with
  | nil => simp [Args.length]
  | cons x xs =>
    cases n with
    | zero => simp [Args.get] at h
    | succ n =>
      have hh := getNoneLength xs n h
      simpa [Args.length, Nat.add_comm] using Nat.succ_le_succ hh
termination_by sizeOf values

theorem insertedAtDepth : InsertionTargets.InsertedAtDepth := by
  intro v rest σ depth
  simp [substitute, Args.get]

theorem retainedLocalIndex : InsertionTargets.RetainedLocalIndex := by
  intro values σ i depth hi
  simp [substitute, hi]

theorem boundUnderBinder : InsertionTargets.BoundUnderBinder := by
  intro values σ i depth
  by_cases hi : i < depth
  · have hi' : i+1 < depth+1 := Nat.succ_lt_succ hi
    simp [substitute, hi, hi', shift]
  · have hi' : ¬ i+1 < depth+1 := fun h => hi (Nat.lt_of_succ_lt_succ h)
    cases hv : values.get (i-depth) with
    | some v =>
      simp only [substitute, hi, hi', if_false, Nat.add_sub_add_right, hv]
      exact (SubstitutionProof.shiftAdd v 1 depth 0).symm
    | none =>
      have hlen : values.length ≤ i :=
        Nat.le_trans (getNoneLength values (i-depth) hv) (Nat.sub_le i depth)
      simp [substitute, hi, hi', Nat.add_sub_add_right, hv, shift, Nat.succ_sub hlen]
end LogicLineages.PersistentMarking.InsertionProof
