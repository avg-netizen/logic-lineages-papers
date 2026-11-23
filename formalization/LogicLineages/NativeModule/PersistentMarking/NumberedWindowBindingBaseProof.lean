module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowBindingTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowBindingBaseProof
open NumberedWindowSyntax

theorem getNoneLength (values : NArgs) (i : Nat) (h : values.get i = none) :
    values.length ≤ i := by
  cases values with
  | nil => exact Nat.zero_le i
  | cons a rest =>
    cases i with
    | zero => cases h
    | succ i =>
      have hi := getNoneLength rest i h
      simp only [NArgs.length]
      omega
termination_by sizeOf values

theorem singletonPast (a : NTerm) (i : Nat) (h : i ≠ 0) :
    (NArgs.cons a .nil).get i = none := by
  cases i with
  | zero => exact (h rfl).elim
  | succ i => rfl

mutual
theorem shiftZero (Q : NTerm) (cutoff : Nat) : shift 0 cutoff Q = Q := by
  cases Q with
  | free σ x => rfl
  | bound σ i => simp [shift]
  | lam σ Q => simp only [shift,shiftZero Q]
  | bottom σ => rfl
  | ordinary f bs => simp only [shift,shiftArgsZero bs]
  | numbered f τ k bs es => simp only [shift,shiftArgsZero bs,shiftArgsZero es]
  | auxApp σ τ q a => simp only [shift,shiftZero q,shiftZero a]
termination_by sizeOf Q

theorem shiftArgsZero (As : NArgs) (cutoff : Nat) : shiftArgs 0 cutoff As = As := by
  cases As with
  | nil => rfl
  | cons a tail => simp only [shiftArgs,shiftZero a,shiftArgsZero tail]
termination_by sizeOf As
end

theorem substituteAppend (values : NArgs) (depth : Nat) (left right : NArgs) :
    substituteArgs values depth (left.append right) =
      (substituteArgs values depth left).append (substituteArgs values depth right) := by
  cases left with
  | nil => rfl
  | cons a left => simp only [NArgs.append,substituteArgs,substituteAppend values depth left right]
termination_by sizeOf left

theorem substituteBoundZero (a : NTerm) (σ : Ty) :
    substitute (.cons a .nil) 0 (.bound σ 0) = a := by
  change shift 0 0 a = a
  exact shiftZero a 0

end LogicLineages.PersistentMarking.NumberedWindowBindingBaseProof
