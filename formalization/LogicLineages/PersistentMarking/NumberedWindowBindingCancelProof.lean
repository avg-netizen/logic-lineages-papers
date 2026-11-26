import LogicLineages.PersistentMarking.NumberedWindowBindingBaseProof

namespace LogicLineages.PersistentMarking.NumberedWindowBindingCancelProof
open NumberedWindowSyntax NumberedWindowBindingBaseProof

private theorem cancelBound (a : NTerm) (k cutoff : Nat) (σ : Ty) (i : Nat) :
    substitute (.cons a .nil) (k+cutoff) (shift (k+1) cutoff (.bound σ i)) =
      shift k cutoff (.bound σ i) := by
  by_cases hi : i < cutoff
  · have hj : i < k + cutoff := by omega
    simp only [shift,hi,if_true,substitute,hj]
  · have hj : ¬ i + (k+1) < k+cutoff := by omega
    have hzero : i+(k+1)-(k+cutoff) ≠ 0 := by omega
    have hg := singletonPast a _ hzero
    simp only [shift,hi,if_false,substitute,hj,hg,NArgs.length]
    congr 1 <;> omega

mutual
theorem cancel (a : NTerm) (k cutoff : Nat) (Q : NTerm) :
    substitute (.cons a .nil) (k+cutoff) (shift (k+1) cutoff Q) = shift k cutoff Q := by
  cases Q with
  | free σ x => rfl
  | bound σ i => exact cancelBound a k cutoff σ i
  | lam σ Q =>
    simp only [shift,substitute]
    rw [show k+cutoff+1 = k+(cutoff+1) by omega,cancel a k (cutoff+1) Q]
  | bottom σ => rfl
  | ordinary f bs => simp only [shift,substitute,cancelArgs a k cutoff bs]
  | numbered f τ j bs es =>
    simp only [shift,substitute,cancelArgs a k cutoff bs,cancelArgs a k cutoff es]
  | auxApp σ τ q b =>
    simp only [shift,substitute,cancel a k cutoff q,cancel a k cutoff b]
termination_by sizeOf Q

theorem cancelArgs (a : NTerm) (k cutoff : Nat) (As : NArgs) :
    substituteArgs (.cons a .nil) (k+cutoff) (shiftArgs (k+1) cutoff As) = shiftArgs k cutoff As := by
  cases As with
  | nil => rfl
  | cons b tail => simp only [shiftArgs,substituteArgs,cancel a k cutoff b,cancelArgs a k cutoff tail]
termination_by sizeOf As
end

end LogicLineages.PersistentMarking.NumberedWindowBindingCancelProof
