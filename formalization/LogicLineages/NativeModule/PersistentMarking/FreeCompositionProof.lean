module

public import LogicLineages.NativeModule.PersistentMarking.FreeShiftProof

@[expose] public section

namespace LogicLineages.PersistentMarking.FreeCompositionProof
open Spine

theorem mapLength (θ : FreeMap) (d : Nat) (vs : Args) :
    (freeSubArgs θ d vs).length = vs.length := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [freeSubArgs, Args.length, mapLength θ d vs]
termination_by sizeOf vs

theorem mapGet (θ : FreeMap) (d : Nat) (vs : Args) (i : Nat) :
    (freeSubArgs θ d vs).get i = (vs.get i).map (freeSub θ d) := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    cases i with
    | zero => rfl
    | succ i => exact mapGet θ d vs i
termination_by sizeOf vs

theorem mapAppend (θ : FreeMap) (d : Nat) (xs ys : Args) :
    freeSubArgs θ d (xs.append ys) = (freeSubArgs θ d xs).append (freeSubArgs θ d ys) := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [Args.append, freeSubArgs, mapAppend θ d xs ys]
termination_by sizeOf xs

mutual
 theorem composition (θ : FreeMap) (vs : Args) (d : Nat) (q : Expr) :
    freeSub θ d (substitute vs d q) =
      substitute (freeSubArgs θ 0 vs) d (freeSub θ (d+vs.length) q) := by
  cases q with
  | free σ x =>
    simp only [substitute, freeSub]
    simpa only [Nat.add_zero, mapLength] using
      (FreeShiftProof.cancellation (freeSubArgs θ 0 vs) d 0 (θ σ x)).symm
  | bound σ i =>
    by_cases hi : i < d
    · simp [substitute, hi, freeSub]
    · cases hg : vs.get (i-d) with
      | none => simp [substitute, hi, hg, freeSub, mapGet, mapLength]
      | some v =>
        simp only [substitute, hi, if_false, hg, freeSub, mapGet, Option.map_some]
        simpa only [Nat.add_zero] using FreeShiftProof.freeShift θ d 0 v
  | lam σ body =>
    simp only [substitute, freeSub]
    have h := composition θ vs (d+1) body
    simpa only [Nat.add_assoc, Nat.add_comm 1 vs.length] using congrArg (Expr.lam σ) h
  | head f base => simp only [substitute, freeSub, compositionArgs θ vs d base]
  | marked f τ base extras =>
    simp only [substitute, freeSub, compositionArgs θ vs d base, compositionArgs θ vs d extras]
 termination_by sizeOf q
 theorem compositionArgs (θ : FreeMap) (vs : Args) (d : Nat) (qs : Args) :
    freeSubArgs θ d (substituteArgs vs d qs) =
      substituteArgs (freeSubArgs θ 0 vs) d (freeSubArgs θ (d+vs.length) qs) := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [substituteArgs, freeSubArgs, composition θ vs d q, compositionArgs θ vs d qs]
 termination_by sizeOf qs
end
end LogicLineages.PersistentMarking.FreeCompositionProof
