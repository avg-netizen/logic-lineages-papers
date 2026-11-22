module
public import LogicLineages.PermittedControl.ActualLowerRankChartRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualLowerRankChartRows
open OriginalPrintedTerminalBitClauses (BitRow RowHolds)

private theorem fundHolds (f ρ : Nat → Nat) (B i : Nat) :
    RowHolds f ρ (fundRow B i) ↔ B ≤ ρ i := by
  constructor
  · rintro ⟨_,v,⟨xs,reads,eq⟩,sign⟩
    cases xs with
    | nil => exact False.elim reads
    | cons x xs =>
      cases xs with
      | cons w ws => exact False.elim reads.2.2
      | nil =>
        have seen : x = ρ i := reads.1
        change -(B : Int) + (1 * (x : Int) + 0) = v at eq
        change 0 ≤ v at sign
        omega
  · intro paid
    let v : Int := -(B : Int) + (1 * (ρ i : Int) + 0)
    refine ⟨True.intro,v,⟨[ρ i],⟨rfl,rfl,True.intro⟩,rfl⟩,?_⟩
    change 0 ≤ v
    dsimp [v]
    omega

private theorem risingHolds (f ρ : Nat → Nat) (i : Nat) :
    RowHolds f ρ (risingRow i) ↔ ρ i < ρ (i+1) := by
  constructor
  · rintro ⟨_,v,⟨xs,reads,eq⟩,sign⟩
    cases xs with
    | nil => exact False.elim reads
    | cons x xs =>
      cases xs with
      | nil => exact False.elim reads.2.2
      | cons y ys =>
        cases ys with
        | cons w ws => exact False.elim reads.2.2.2.2
        | nil =>
          have high : x = ρ (i+1) := reads.1
          have low : y = ρ i := reads.2.2.1
          change 0 + (1 * (x : Int) + ((-1) * (y : Int) + 0)) = v at eq
          change 0 < v at sign
          omega
  · intro sorted
    let v : Int := 0 + (1 * (ρ (i+1) : Int) + ((-1) * (ρ i : Int) + 0))
    refine ⟨True.intro,v,⟨[ρ (i+1),ρ i],⟨rfl,rfl,rfl,rfl,True.intro⟩,rfl⟩,?_⟩
    change 0 < v
    dsimp [v]
    omega

private theorem stepsGiveStrict (ρ : Nat → Nat) (top : Nat)
    (steps : ∀ i < top-1, ρ i < ρ (i+1)) (i j : Nat) (lt : i < j) (below : j < top) :
    ρ i < ρ j := by
  induction j generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero i lt)
  | succ j ih =>
    have adjacent := steps j (by omega)
    by_cases eq : i = j
    · simpa only [eq] using adjacent
    · exact (ih i (by omega) (by omega)).trans adjacent

theorem exactLowerRankChartRows : ExactLowerRankChartRows := by
  intro f ρ B top
  refine ⟨?_,?_⟩
  · constructor
    · intro live
      have funded (i : Nat) (h : i < top) : B ≤ ρ i :=
        (fundHolds f ρ B i).mp (live _ (List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)))
      have inc (i : Nat) (h : i < top-1) : ρ i < ρ (i+1) :=
        (risingHolds f ρ i).mp (live _ (List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)))
      exact ⟨funded,stepsGiveStrict ρ top inc⟩
    · rintro ⟨funded,strict⟩ row used
      rcases List.mem_append.mp used with issue | ordered
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp issue
        exact (fundHolds f ρ B i).mpr (funded i (List.mem_range.mp hi))
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ordered
        have idx := List.mem_range.mp hi
        exact (risingHolds f ρ i).mpr (strict i (i+1) (by omega) (by omega))
  · intro row used
    rcases List.mem_append.mp used with issue | ordered
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp issue
      refine ⟨rfl,?_⟩
      intro t ht
      have eq := List.mem_singleton.mp ht
      subst t
      exact List.mem_range.mp hi
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ordered
      have idx := List.mem_range.mp hi
      refine ⟨rfl,?_⟩
      intro t ht
      have disj : t = (1,.coordinate (i+1)) ∨ t = (-1,.coordinate i) := by
        simpa only [risingRow,List.mem_cons,List.not_mem_nil,or_false] using ht
      rcases disj with rfl | rfl
      · change i+1 < top; omega
      · change i < top; omega

end LogicLineages.PermittedControl.ActualLowerRankChartRows
