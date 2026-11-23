module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowBindingCancelProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowBindingPushProof
open NumberedWindowSyntax NumberedWindowBindingBaseProof NumberedWindowBindingCancelProof

private theorem pushBound (a : NTerm) (values : NArgs) (d : Nat) (σ : Ty) (i : Nat) :
    substitute (.cons a .nil) d (substitute values (d+1) (.bound σ i)) =
      substitute (.cons a values) d (.bound σ i) := by
  by_cases hlo : i < d
  · have hinner : i < d+1 := by omega
    simp only [substitute,hlo,hinner,if_true]
  · by_cases heq : i = d
    · subst i
      have hinner : d < d+1 := by omega
      simp only [substitute,hlo,hinner,if_true,if_false,Nat.sub_self,NArgs.get]
    · have hinner : ¬ i < d+1 := by omega
      have hidx : i-d = (i-(d+1))+1 := by omega
      cases hval : values.get (i-(d+1)) with
      | some v =>
        simp only [substitute,hinner,hlo,if_false,hval,hidx,NArgs.get]
        simpa only [Nat.add_zero] using cancel a d 0 v
      | none =>
        have hlen := getNoneLength values _ hval
        have hrem : ¬ i - values.length < d := by omega
        have hnz : i-values.length-d ≠ 0 := by omega
        have hg := singletonPast a _ hnz
        simp only [substitute,hinner,hlo,if_false,hval,hidx,NArgs.get,hrem,hg,NArgs.length]
        congr 1 <;> omega

mutual
theorem push (a : NTerm) (values : NArgs) (depth : Nat) (Q : NTerm) :
    substitute (.cons a .nil) depth (substitute values (depth+1) Q) =
      substitute (.cons a values) depth Q := by
  cases Q with
  | free σ x => rfl
  | bound σ i => exact pushBound a values depth σ i
  | lam σ Q => simp only [substitute,push a values (depth+1) Q]
  | bottom σ => rfl
  | ordinary f bs => simp only [substitute,pushArgs a values depth bs]
  | numbered f τ k bs es =>
    simp only [substitute,pushArgs a values depth bs,pushArgs a values depth es]
  | auxApp σ τ q b => simp only [substitute,push a values depth q,push a values depth b]
termination_by sizeOf Q

theorem pushArgs (a : NTerm) (values : NArgs) (depth : Nat) (As : NArgs) :
    substituteArgs (.cons a .nil) depth (substituteArgs values (depth+1) As) =
      substituteArgs (.cons a values) depth As := by
  cases As with
  | nil => rfl
  | cons b tail => simp only [substituteArgs,push a values depth b,pushArgs a values depth tail]
termination_by sizeOf As
end

end LogicLineages.PersistentMarking.NumberedWindowBindingPushProof
