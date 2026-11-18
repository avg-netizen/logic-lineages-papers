module
public import LogicLineages.StandardControlCurrent.MixedCancellationTargets
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedCancellation
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm

theorem enumeration : MixedCancellationTargets.Enumeration := by
  intro n
  induction n with
  | zero => intro bs; simp [masks]
  | succ n ih =>
      intro bs
      cases bs with
      | nil => simp [masks]
      | cons b bs =>
          cases b <;> simp [masks,ih]

private theorem split_sum (xs : List (Int × Summand)) (bs : List Bool)
    (h : bs.length = xs.length) (ν : Nat → Nat) :
    (xs.map (fun a => a.1*(a.2.term.value ν : Int))).sum =
      (((xs.zip bs).filterMap (fun a => if a.2 then none else some a.1)).map
        (fun a => a.1*(a.2.term.value ν : Int))).sum +
      (((xs.zip bs).filterMap (fun a => if a.2 then some a.1 else none)).map
        (fun a => a.1*(a.2.term.value ν : Int))).sum := by
  induction xs generalizing bs with
  | nil =>
      have hb : bs = [] := List.length_eq_zero.mp h
      subst bs
      simp
  | cons a xs ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          have ht : bs.length = xs.length := Nat.succ.inj h
          have hs := ih bs ht
          cases b <;> simp at * <;> omega

theorem partition : MixedCancellationTargets.Partition := by
  intro r bs h ν
  have hs := split_sum r.2 bs h ν
  simp only [rowValue,retained,selected]
  omega
end LogicLineages.StandardControlCurrent.MixedCancellation
