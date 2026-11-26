module
public import LogicLineages.PermittedControl.ActualLinearExitTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualLinearExit
open PreparedProjection ActualMixedRowLeadingAnnotations ActualZeroClassReplacement

private theorem readUnchanged (f ρ : Nat → Nat) (zRank z : Nat) (op : LowerOperand)
    (different : op.rank ≠ zRank) :
    lowerOperandRead f (Function.update ρ zRank z) op = lowerOperandRead f ρ op := by
  cases op <;> simp only [LowerOperand.rank] at different <;>
    simp only [lowerOperandRead, Function.update_of_ne different]

theorem linearOfNotNonlinear (op : LowerOperand) (absent : ¬ NonlinearOperand op) :
    LinearOperand op := by
  cases op with
  | coordinate rank => exact True.intro
  | count rank lam mu => exact (absent True.intro).elim
  | ordinary rank F =>
      cases F with
      | iterate n =>
          cases n with
          | zero => exact True.intro
          | succ n => exact (absent (Nat.succ_pos n)).elim
      | entry n lam mu => exact (absent True.intro).elim

private theorem linearValue (f ρ : Nat → Nat) (op : LowerOperand) (v : Nat)
    (linear : LinearOperand op) (actual : LowerOperandActual f ρ op v) : v = ρ op.rank := by
  cases op with
  | coordinate rank => exact actual
  | count rank lam mu => exact False.elim linear
  | ordinary rank F =>
      cases F with
      | entry a lam mu => exact False.elim linear
      | iterate a =>
          cases a with
          | succ a => exact False.elim linear
          | zero => exact actual.2

private theorem linearActual (f ρ : Nat → Nat) (op : LowerOperand)
    (linear : LinearOperand op) : LowerOperandActual f ρ op (ρ op.rank) := by
  cases op with
  | coordinate rank => rfl
  | count rank lam mu => exact False.elim linear
  | ordinary rank F =>
      cases F with
      | entry a lam mu => exact False.elim linear
      | iterate a =>
          cases a with
          | succ a => exact False.elim linear
          | zero => exact ⟨True.intro,rfl⟩

theorem replayPaid (f ρ : Nat → Nat) (zRank z : Nat) (xs : List Read)
    (reads : liftedReads f ρ xs)
    (linear : ∀ rd ∈ xs, rd.1.2.rank = zRank → LinearOperand rd.1.2) :
    liftedReads f (Function.update ρ zRank z) (replay zRank z xs) := by
  induction xs with
  | nil => exact True.intro
  | cons rd xs ih =>
      have tail := ih reads.2.2 (fun rd hr => linear rd (List.mem_cons_of_mem _ hr))
      by_cases atZ : rd.1.2.rank = zRank
      · have actual : LowerOperandActual f (Function.update ρ zRank z) rd.1.2 z := by
          have h := linearActual f (Function.update ρ zRank z) rd.1.2
            (linear rd List.mem_cons_self atZ)
          simpa only [atZ, Function.update_self] using h
        simp only [replay, if_pos atZ]
        exact ⟨actual, (preparedTiedProjection.1 _ _ _ _).mpr actual, tail⟩
      · have hit : lowerOperandRead f (Function.update ρ zRank z) rd.1.2 = some (some rd.2) :=
          (readUnchanged f ρ zRank z rd.1.2 atZ).trans reads.2.1
        simp only [replay, if_neg atZ]
        exact ⟨(preparedTiedProjection.1 _ _ _ _).mp hit, hit, tail⟩

theorem replaySelf (f ρ : Nat → Nat) (zRank : Nat) (xs : List Read)
    (reads : liftedReads f ρ xs)
    (linear : ∀ rd ∈ xs, rd.1.2.rank = zRank → LinearOperand rd.1.2) :
    replay zRank (ρ zRank) xs = xs := by
  induction xs with
  | nil => rfl
  | cons rd xs ih =>
      have tail := ih reads.2.2 (fun rd hr => linear rd (List.mem_cons_of_mem _ hr))
      by_cases atZ : rd.1.2.rank = zRank
      · have v : rd.2 = ρ zRank :=
          (linearValue f ρ rd.1.2 rd.2 (linear rd List.mem_cons_self atZ) reads.1)
            |>.trans (congrArg ρ atZ)
        simp only [replay, if_pos atZ, tail]
        exact congrArg (fun head : Read => head :: xs) (Prod.ext rfl v.symm)
      · simp only [replay, if_neg atZ, tail]

end LogicLineages.PermittedControl.ActualLinearExit
