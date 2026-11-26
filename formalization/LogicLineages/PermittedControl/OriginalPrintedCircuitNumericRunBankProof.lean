module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRun
open OriginalPrintedCircuitNumericRead (RawGate bank)

private theorem setLength (values : List Nat) (i v : Nat) :
    (values.set i v).length = values.length := by
  induction values generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simp only [List.set_cons_succ,List.length_cons,ih]

private theorem setBank (values : List Nat) (i v : Nat) (inRange : i < values.length) :
    bank (values.set i v) = Function.update (bank values) i v := by
  induction values generalizing i with
  | nil => exact (Nat.not_lt_zero _ inRange).elim
  | cons x xs ih =>
      funext n
      cases i with
      | zero =>
          cases n with
          | zero => simp only [Function.update_self] <;> rfl
          | succ n =>
              rw [Function.update_of_ne (Nat.succ_ne_zero _)] <;> rfl
      | succ i =>
          have bound : i < xs.length := Nat.lt_of_succ_lt_succ inRange
          cases n with
          | zero =>
              rw [Function.update_of_ne ((Nat.succ_ne_zero _).symm)] <;> rfl
          | succ n =>
              have tail := congrFun (ih i bound) n
              by_cases h : n = i
              · subst n
                simp only [Function.update_self] at tail ⊢
                simpa only [bank,List.set_cons_succ,List.getD_cons_succ] using tail
              · rw [Function.update_of_ne h] at tail
                rw [Function.update_of_ne (Nat.succ_ne_succ.mpr h)]
                simpa only [bank,List.set_cons_succ,List.getD_cons_succ] using tail

theorem exactNumericBankUpdates : ExactNumericBankUpdates := ⟨setLength,setBank⟩

theorem foldError (f : Nat → Nat) (gates : List RawGate) (why : Nat) :
    gates.foldl (fun st g => stepCarry f (st,g)) (Sum.inl why) = Sum.inl why := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      exact ih

theorem exactNumericRunBehavior : ExactNumericRunBehavior := by
  constructor
  · intro f values g out
    simp only [step,if_neg (Nat.not_lt_of_ge out)]
  · intro f values doneGates suffix why stop
    change (doneGates ++ suffix).foldl (fun st g => stepCarry f (st,g)) (Sum.inr values) = Sum.inl why
    rw [List.foldl_append]
    change suffix.foldl (fun st g => stepCarry f (st,g)) (runCode f (values,doneGates)) = _
    rw [stop]
    exact foldError f suffix why

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRun
