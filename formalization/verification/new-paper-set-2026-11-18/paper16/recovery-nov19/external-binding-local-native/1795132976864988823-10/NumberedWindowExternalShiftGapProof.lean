import LogicLineages.PersistentMarking.NumberedWindowExternalBindingNaturalityTargets
import LogicLineages.PersistentMarking.NumberedWindowBindingBaseProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalShiftGapProof
open NumberedWindowSyntax NumberedWindowBindingBaseProof

private theorem mergeBound (σ : Ty) (i n k c t : Nat) (h : c ≤ k) :
    shift n (c+t) (shift k t (.bound σ i)) = shift (k+n) t (.bound σ i) := by
  by_cases hi : i < t
  · have hc : i < c+t := by omega
    simp [shift,hi,hc]
  · have hc : ¬ i+k < c+t := by omega
    simp [shift,hi,hc,Nat.add_assoc]

mutual
theorem merge (q : NTerm) (n k c t : Nat) (h : c ≤ k) :
    shift n (c+t) (shift k t q) = shift (k+n) t q := by
  cases q with
  | free | bottom => rfl
  | bound σ i => exact mergeBound σ i n k c t h
  | lam σ q => simpa only [shift,Nat.add_assoc] using
      congrArg (NTerm.lam σ) (merge q n k c (t+1) h)
  | ordinary f bs => simp only [shift,mergeArgs bs n k c t h]
  | numbered f τ l bs es => simp only [shift,mergeArgs bs n k c t h,mergeArgs es n k c t h]
  | auxApp σ τ q a => simp only [shift,merge q n k c t h,merge a n k c t h]
termination_by sizeOf q
theorem mergeArgs (xs : NArgs) (n k c t : Nat) (h : c ≤ k) :
    shiftArgs n (c+t) (shiftArgs k t xs) = shiftArgs (k+n) t xs := by
  cases xs with
  | nil => rfl
  | cons q qs => simp only [shiftArgs,merge q n k c t h,mergeArgs qs n k c t h]
termination_by sizeOf xs
end

private theorem removeBound (σ : Ty) (i : Nat) (a : NTerm) (k s c : Nat) (h : k ≤ s) :
    substitute (.cons a .nil) (k+c) (shift (s+1) c (.bound σ i)) = shift s c (.bound σ i) := by
  by_cases hi : i < c
  · have hk : i < k+c := by omega
    simp [shift,hi,substitute,hk]
  · have hk : ¬ i+(s+1) < k+c := by omega
    have hn : i+(s+1)-(k+c) ≠ 0 := by omega
    simp only [shift,hi,if_false,substitute,hk,singletonPast a _ hn,NArgs.length]
    congr 1 <;> omega

mutual
theorem remove (q : NTerm) (a : NTerm) (k s c : Nat) (h : k ≤ s) :
    substitute (.cons a .nil) (k+c) (shift (s+1) c q) = shift s c q := by
  cases q with
  | free | bottom => rfl
  | bound σ i => exact removeBound σ i a k s c h
  | lam σ q => simpa only [shift,substitute,Nat.add_assoc] using
      congrArg (NTerm.lam σ) (remove q a k s (c+1) h)
  | ordinary f bs => simp only [shift,substitute,removeArgs bs a k s c h]
  | numbered f τ l bs es => simp only [shift,substitute,removeArgs bs a k s c h,removeArgs es a k s c h]
  | auxApp σ τ q b => simp only [shift,substitute,remove q a k s c h,remove b a k s c h]
termination_by sizeOf q
theorem removeArgs (xs : NArgs) (a : NTerm) (k s c : Nat) (h : k ≤ s) :
    substituteArgs (.cons a .nil) (k+c) (shiftArgs (s+1) c xs) = shiftArgs s c xs := by
  cases xs with
  | nil => rfl
  | cons q qs => simp only [shiftArgs,substituteArgs,remove q a k s c h,removeArgs qs a k s c h]
termination_by sizeOf xs
end

end LogicLineages.PersistentMarking.NumberedWindowExternalShiftGapProof
