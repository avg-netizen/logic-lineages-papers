module
public import LogicLineages.PermittedControl.SignedRowSliceValueTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowSliceValue
open MixedSameRankResidue (WeightedOperand orderedReads actualSum)
open SignedRowCoordinateSlice (selected untouched)

theorem splitAndRejoin : SplitAndRejoin := by
  intro f ρ rank terms total
  induction terms generalizing total with
  | nil =>
    constructor
    · rintro ⟨values,reads,sum⟩
      cases values with
      | nil => exact ⟨[],[],True.intro,True.intro,sum⟩
      | cons _ _ => exact False.elim reads
    · rintro ⟨taken,kept,paid,retained,sum⟩
      cases taken with
      | cons _ _ => exact False.elim paid
      | nil =>
        cases kept with
        | nil => exact ⟨[],True.intro,sum⟩
        | cons _ _ => exact False.elim retained
  | cons t ts ih =>
    by_cases atRank : t.2.rank = rank
    · have takeHead : selected rank (t :: ts) = t :: selected rank ts := by simp [selected,atRank]
      have retainTail : untouched rank (t :: ts) = untouched rank ts := by simp [untouched,atRank]
      rw [takeHead,retainTail]
      constructor
      · rintro ⟨values,reads,meaning⟩
        cases values with
        | nil => exact False.elim reads
        | cons v vs =>
          obtain ⟨actual,read,tail⟩ := reads
          obtain ⟨taken,kept,paid,retained,sum⟩ := (ih (actualSum ts vs)).mp ⟨vs,tail,rfl⟩
          refine ⟨v :: taken,kept,⟨actual,read,paid⟩,retained,?_⟩
          change (t.1 * (v : Int) + actualSum (selected rank ts) taken) +
            actualSum (untouched rank ts) kept = total
          rw [add_assoc,sum]
          exact meaning
      · rintro ⟨taken,kept,paid,retained,sum⟩
        cases taken with
        | nil => exact False.elim paid
        | cons v values =>
          obtain ⟨actual,read,paidTail⟩ := paid
          obtain ⟨tail,reads,tailSum⟩ :=
            (ih (actualSum (selected rank ts) values + actualSum (untouched rank ts) kept)).mpr
              ⟨values,kept,paidTail,retained,rfl⟩
          refine ⟨v :: tail,⟨actual,read,reads⟩,?_⟩
          change t.1 * (v : Int) + actualSum ts tail = total
          rw [tailSum]
          change (t.1 * (v : Int) + actualSum (selected rank ts) values) +
            actualSum (untouched rank ts) kept = total at sum
          simpa only [add_assoc] using sum
    · have takeTail : selected rank (t :: ts) = selected rank ts := by simp [selected,atRank]
      have keepHead : untouched rank (t :: ts) = t :: untouched rank ts := by simp [untouched,atRank]
      rw [takeTail,keepHead]
      constructor
      · rintro ⟨values,reads,meaning⟩
        cases values with
        | nil => exact False.elim reads
        | cons v vs =>
          obtain ⟨actual,read,tail⟩ := reads
          obtain ⟨taken,kept,paid,retained,sum⟩ := (ih (actualSum ts vs)).mp ⟨vs,tail,rfl⟩
          refine ⟨taken,v :: kept,paid,⟨actual,read,retained⟩,?_⟩
          change actualSum (selected rank ts) taken +
            (t.1 * (v : Int) + actualSum (untouched rank ts) kept) = total
          calc
            _ = t.1 * (v : Int) +
                (actualSum (selected rank ts) taken + actualSum (untouched rank ts) kept) := by ac_rfl
            _ = t.1 * (v : Int) + actualSum ts vs := congrArg (t.1 * (v : Int) + ·) sum
            _ = total := meaning
      · rintro ⟨taken,kept,paid,retained,sum⟩
        cases kept with
        | nil => exact False.elim retained
        | cons v values =>
          obtain ⟨actual,read,retainedTail⟩ := retained
          obtain ⟨tail,reads,tailSum⟩ :=
            (ih (actualSum (selected rank ts) taken + actualSum (untouched rank ts) values)).mpr
              ⟨taken,values,paid,retainedTail,rfl⟩
          refine ⟨v :: tail,⟨actual,read,reads⟩,?_⟩
          change t.1 * (v : Int) + actualSum ts tail = total
          rw [tailSum]
          calc
            _ = actualSum (selected rank ts) taken +
                (t.1 * (v : Int) + actualSum (untouched rank ts) values) := by ac_rfl
            _ = total := sum

end LogicLineages.PermittedControl.SignedRowSliceValue
