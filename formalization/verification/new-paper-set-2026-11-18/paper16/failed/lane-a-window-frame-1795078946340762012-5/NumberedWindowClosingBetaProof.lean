import LogicLineages.PersistentMarking.NumberedWindowClosingShiftProof
import LogicLineages.PersistentMarking.NumberedWindowBindingBaseProof

namespace LogicLineages.PersistentMarking.NumberedWindowClosingBetaProof
open NumberedWindowSyntax NumberedWindowClosing
open NumberedWindowBindingBaseProof (singletonPast)
open NameBridge (Name)

private theorem freeCase (n : Name) (outer c : Nat) (σ : Ty) (x : Nat) (a : NTerm) :
    closeAt n (outer+c) (substitute (.cons a .nil) c (.free σ x)) =
      substitute (.cons (closeAt n outer a) .nil) c (closeAt n (outer+c+1) (.free σ x)) := by
  by_cases h : (σ,x) = n
  · have hlt : ¬ outer+c+1 < c := by omega
    have hi : outer+c+1-c ≠ 0 := by omega
    have hg := singletonPast (closeAt n outer a) _ hi
    simp only [substitute,closeAt,h,if_true,hlt,if_false,hg,NArgs.length,Nat.add_zero,Nat.add_sub_cancel]
  · simp only [substitute,closeAt,h,if_false]

private theorem boundCase (n : Name) (outer c : Nat) (σ : Ty) (i : Nat) (a : NTerm) :
    closeAt n (outer+c) (substitute (.cons a .nil) c (.bound σ i)) =
      substitute (.cons (closeAt n outer a) .nil) c (closeAt n (outer+c+1) (.bound σ i)) := by
  by_cases hi : i < c
  · simp only [substitute,closeAt,hi,if_true]
  · by_cases he : i = c
    · subst i
      simp only [substitute,closeAt,Nat.lt_irrefl,if_false,Nat.sub_self,NArgs.get]
      exact NumberedWindowClosingShiftProof.term n outer c 0 (Nat.zero_le _) a
    · have hp : i-c ≠ 0 := by omega
      have hq := singletonPast a _ hp
      have hr := singletonPast (closeAt n outer a) _ hp
      simp only [substitute,closeAt,hi,if_false,hq,hr]

mutual
theorem term (n : Name) (outer c : Nat) (q a : NTerm) :
    closeAt n (outer+c) (substitute (.cons a .nil) c q) =
      substitute (.cons (closeAt n outer a) .nil) c (closeAt n (outer+c+1) q) := by
  cases q with
  | free σ x => exact freeCase n outer c σ x a
  | bound σ i => exact boundCase n outer c σ i a
  | lam σ q =>
    simp only [substitute,closeAt]
    rw [show outer+c+1 = outer+(c+1) by omega]
    exact congrArg (NTerm.lam σ) (term n outer (c+1) q a)
  | bottom σ => rfl
  | ordinary f bs => simp only [substitute,closeAt,args n outer c bs a]
  | numbered f τ k bs es => simp only [substitute,closeAt,args n outer c bs a,args n outer c es a]
  | auxApp σ τ q b => simp only [substitute,closeAt,term n outer c q a,term n outer c b a]
termination_by sizeOf q

theorem args (n : Name) (outer c : Nat) (As : NArgs) (a : NTerm) :
    closeArgsAt n (outer+c) (substituteArgs (.cons a .nil) c As) =
      substituteArgs (.cons (closeAt n outer a) .nil) c (closeArgsAt n (outer+c+1) As) := by
  cases As with
  | nil => rfl
  | cons q qs =>
    simp only [substituteArgs,closeArgsAt,term n outer c q a,args n outer c qs a]
termination_by sizeOf As
end

end LogicLineages.PersistentMarking.NumberedWindowClosingBetaProof
