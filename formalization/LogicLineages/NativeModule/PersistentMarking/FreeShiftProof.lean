module

public import LogicLineages.NativeModule.PersistentMarking.FreeCovarianceTargets
public import LogicLineages.NativeModule.PersistentMarking.SubstitutionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.FreeShiftProof
open Spine

theorem getBeyond (vs : Args) (i : Nat) (hi : vs.length ≤ i) : vs.get i = none := by
  cases vs with
  | nil => rfl
  | cons v rest =>
    cases i with
    | zero => simp [Args.length] at hi
    | succ i =>
      have h : rest.length ≤ i := by simp only [Args.length] at hi; omega
      exact getBeyond rest i h
termination_by sizeOf vs

mutual
 theorem insertedShift (t : Expr) (a b c : Nat) :
    shift a (b+c) (shift b c t) = shift (b+a) c t := by
  cases t with
  | free σ x => rfl
  | bound σ i =>
    by_cases h : i < c
    · have h' : i < b+c := by omega
      simp [shift, h, h']
    · have h' : ¬ i+b < b+c := by omega
      simp [shift, h, h', Nat.add_assoc]
  | lam σ body =>
    simp only [shift]
    rw [show b+c+1 = b+(c+1) by omega, insertedShift body]
  | head f base => simp only [shift, insertedShiftArgs base]
  | marked f τ base extras => simp only [shift, insertedShiftArgs base, insertedShiftArgs extras]
 termination_by sizeOf t
 theorem insertedShiftArgs (ts : Args) (a b c : Nat) :
    shiftArgs a (b+c) (shiftArgs b c ts) = shiftArgs (b+a) c ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [shiftArgs, insertedShift t, insertedShiftArgs ts]
 termination_by sizeOf ts
end

mutual
 theorem cancellation (vs : Args) (k c : Nat) (t : Expr) :
    substitute vs (k+c) (shift (k+vs.length) c t) = shift k c t := by
  cases t with
  | free σ x => rfl
  | bound σ i =>
    by_cases h : i < c
    · have h' : i < k+c := by omega
      simp [shift, substitute, h, h']
    · have h' : ¬ i+(k+vs.length) < k+c := by omega
      have hg : vs.get (i+(k+vs.length)-(k+c)) = none :=
        getBeyond _ _ (by omega)
      simp [shift, h, substitute, h', hg]
      omega
  | lam σ body =>
    simp only [shift, substitute]
    rw [show k+c+1 = k+(c+1) by omega, cancellation vs k (c+1) body]
  | head f base => simp only [shift, substitute, cancellationArgs vs k c base]
  | marked f τ base extras =>
    simp only [shift, substitute, cancellationArgs vs k c base, cancellationArgs vs k c extras]
 termination_by sizeOf t
 theorem cancellationArgs (vs : Args) (k c : Nat) (ts : Args) :
    substituteArgs vs (k+c) (shiftArgs (k+vs.length) c ts) = shiftArgs k c ts := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [shiftArgs, substituteArgs, cancellation vs k c t, cancellationArgs vs k c ts]
 termination_by sizeOf ts
end

mutual
 theorem freeShift (θ : FreeMap) (k d : Nat) (t : Expr) :
    freeSub θ (k+d) (shift k d t) = shift k d (freeSub θ d t) := by
  cases t with
  | free σ x =>
    simp only [shift, freeSub]
    simpa [Nat.add_comm] using (insertedShift (θ σ x) k d 0).symm
  | bound σ i => simp only [shift, freeSub]
  | lam σ body =>
    simp only [shift, freeSub]
    rw [show k+d+1 = k+(d+1) by omega, freeShift θ k (d+1) body]
  | head f base => simp only [shift, freeSub, freeShiftArgs θ k d base]
  | marked f τ base extras => simp only [shift, freeSub, freeShiftArgs θ k d base, freeShiftArgs θ k d extras]
 termination_by sizeOf t
 theorem freeShiftArgs (θ : FreeMap) (k d : Nat) (ts : Args) :
    freeSubArgs θ (k+d) (shiftArgs k d ts) = shiftArgs k d (freeSubArgs θ d ts) := by
  cases ts with
  | nil => rfl
  | cons t ts => simp only [shiftArgs, freeSubArgs, freeShift θ k d t, freeShiftArgs θ k d ts]
 termination_by sizeOf ts
end
end LogicLineages.PersistentMarking.FreeShiftProof
