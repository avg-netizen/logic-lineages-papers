module
public import LogicLineages.PermittedControl.ActualLinearExitTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualLinearExit
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open NormalForm PreparedProjection ActualZeroClassReplacement

private theorem namesShape (n : Nat) (xs : List Read) (s : Int × Summand)
    (member : s ∈ namedTerms n xs) :
    ∃ j, s.2 = .variable j ∧ n ≤ j ∧ j < n + xs.length := by
  induction xs generalizing n with
  | nil => cases member
  | cons rd xs ih =>
      change s ∈ (rd.1.1,.variable n) :: namedTerms (n+1) xs at member
      rcases List.mem_cons.mp member with atHead | later
      · subst s
        exact ⟨n,rfl,le_rfl,by simp⟩
      · obtain ⟨j,shape,lower,upper⟩ := ih (n+1) later
        exact ⟨j,shape,by omega,by simp only [List.length_cons]; omega⟩

theorem exitPrepared (zRank : Nat) (constant : Int) (xs : List Read) :
    PreparedInput (table zRank xs) (.atom (.nonnegative (exitRow zRank constant xs))) := by
  let row := exitRow zRank constant xs
  have shape (s : Int × Summand) (member : s ∈ row.2) :
      ∃ j, s.2 = .variable j ∧ j ≤ (table zRank xs).length := by
    change s ∈ (slope zRank xs,.variable 0) :: namedTerms 1 (lowerReads zRank xs) at member
    rcases List.mem_cons.mp member with atHead | later
    · subst s
      exact ⟨0,rfl,Nat.zero_le _⟩
    · obtain ⟨j,sj,_,bound⟩ := namesShape 1 (lowerReads zRank xs) s later
      refine ⟨j,sj,?_⟩
      simp only [table,List.length_map]
      omega
  constructor
  · intro a member s hs
    simp only [LinearRows.atoms,List.mem_singleton] at member
    subst a
    obtain ⟨j,sj,_⟩ := shape s hs
    exact ⟨j,sj⟩
  · intro j member
    change j ∈ row.2.map (fun s => s.2.name) at member
    obtain ⟨s,hs,equal⟩ := List.mem_map.mp member
    obtain ⟨i,si,hi⟩ := shape s hs
    rw [si] at equal
    change i = j at equal
    exact equal ▸ hi

private theorem sumCons (rd : Read) (xs : List Read) :
    readSum (rd :: xs) = rd.1.1 * (rd.2 : Int) + readSum xs := rfl

private theorem namedSum (ν : Nat → Nat) (n : Nat) (xs : List Read)
    (values : ∀ (j : Nat) (hj : j < xs.length), ν (n+j) = xs[j].2) :
    ((namedTerms n xs).map (fun s => s.1 * (s.2.term.value ν : Int))).sum = readSum xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons rd xs ih =>
      have head : ν n = rd.2 := by
        have indexZero : 0 < (rd :: xs).length := Nat.zero_lt_succ _
        have atZero := values 0 indexZero
        have item : (rd :: xs)[0]'indexZero = rd := List.getElem_cons_zero rd xs indexZero
        simpa only [Nat.add_zero] using atZero.trans (congrArg (fun r : Read => r.2) item)
      have later (j : Nat) (hj : j < xs.length) : ν (n+1+j) = xs[j].2 := by
        rw [show n+1+j = n+(j+1) by omega]
        have bound : j+1 < (rd :: xs).length := Nat.succ_lt_succ hj
        simpa only [List.getElem_cons_succ] using values (j+1) bound
      simp only [namedTerms,List.map_cons,List.sum_cons,sumCons]
      rw [ih (n+1) later]
      simp only [Summand.term,Term.value,head]

private theorem replaySum (zRank z : Nat) (xs : List Read)
    (bounded : ∀ rd ∈ xs, rd.1.2.rank ≤ zRank) :
    readSum (replay zRank z xs) =
      slope zRank xs * (z : Int) + readSum (lowerReads zRank xs) := by
  induction xs with
  | nil => simp [replay,slope,lowerReads,readSum,MixedSameRankResidue.actualSum]
  | cons rd xs ih =>
      have tail := ih (fun rd hr => bounded rd (List.mem_cons_of_mem _ hr))
      by_cases equal : rd.1.2.rank = zRank
      · have notLower : ¬ rd.1.2.rank < zRank := by rw [equal]; exact Nat.lt_irrefl _
        have lower : lowerReads zRank (rd::xs) = lowerReads zRank xs := by
          simp [lowerReads,notLower]
        rw [lower]
        simp only [slope,replay,if_pos equal,sumCons,tail,add_mul]
        ac_rfl
      · have lt : rd.1.2.rank < zRank :=
          lt_of_le_of_ne (bounded rd List.mem_cons_self) equal
        have lower : lowerReads zRank (rd::xs) = rd :: lowerReads zRank xs := by
          simp [lowerReads,lt]
        rw [lower]
        simp only [slope,replay,if_neg equal,sumCons,tail]
        ac_rfl

theorem rowReplay (ν : Nat → Nat) (zRank z : Nat) (constant : Int) (xs : List Read)
    (bounded : ∀ rd ∈ xs, rd.1.2.rank ≤ zRank)
    (values : OriginalSlots ν (lowerReads zRank xs)) :
    rowValue (exitRow zRank constant xs) (Function.update ν 0 z) =
      constant + readSum (replay zRank z xs) := by
  have same (j : Nat) (hj : j < (lowerReads zRank xs).length) :
      Function.update ν 0 z (1+j) = (lowerReads zRank xs)[j].2 := by
    rw [Function.update_of_ne (show 1+j ≠ 0 by omega)]
    rw [show 1+j = j+1 by omega]
    exact values j hj
  simp only [exitRow,rowValue,List.map_cons,List.sum_cons]
  rw [namedSum _ 1 _ same, replaySum zRank z xs bounded] <;>
    simp only [Summand.term,Term.value,Function.update_self]

end LogicLineages.PermittedControl.ActualLinearExit
