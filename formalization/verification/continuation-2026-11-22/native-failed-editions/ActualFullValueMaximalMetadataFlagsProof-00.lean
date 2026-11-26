module
public import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullValueMaximalMetadata
open ActualFullLabelPairGuards (Answer)

private theorem splitBlock {α : Type} (row tail : List α) :
    (row ++ tail).take row.length = row ∧ (row ++ tail).drop row.length = tail := by
  induction row with
  | nil => simp [List.take,List.drop]
  | cons a rest next => simp [List.take,List.drop,next.1,next.2]

private theorem notLessExact (u v : Nat) : notLess (compare u v) = true ↔ v ≤ u := by
  by_cases lt : u < v
  · simp [compare,notLess,lt,not_le_of_gt lt]
  · have below := Nat.le_of_not_gt lt
    by_cases eq : u = v <;> simp [compare,notLess,lt,eq,below]

private theorem rowFlag (all : List Nat) (C u : Nat) (hu : u ∈ all) (hc : C ∈ all)
    (upper : ∀ v ∈ all, v ≤ C) :
    ((all.map (compare u)).all notLess) = decide (u = C) := by
  have bounds : ((all.map (compare u)).all notLess) = true ↔ u = C := by
    constructor
    · intro yes
      have used : compare u C ∈ all.map (compare u) := List.mem_map.mpr ⟨C,hc,rfl⟩
      exact le_antisymm (upper u hu)
        ((notLessExact u C).mp ((List.all_eq_true.mp yes) _ used))
    · intro eq
      apply List.all_eq_true.mpr
      intro a used
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp used
      exact (notLessExact u v).mpr (eq.symm ▸ upper v hv)
  cases bit : (all.map (compare u)).all notLess <;> by_cases eq : u = C <;>
    simp_all

private theorem flagsBlock (all chosen : List Nat) (C : Nat)
    (present : ∀ u ∈ chosen, u ∈ all) (hc : C ∈ all) (upper : ∀ v ∈ all, v ≤ C) :
    flags all.length chosen.length (chosen.flatMap (fun u => all.map (compare u))) =
      chosen.map (fun v => decide (v = C)) := by
  induction chosen with
  | nil => rfl
  | cons u chosen ih =>
      let row := all.map (compare u)
      let tail := chosen.flatMap (fun v => all.map (compare v))
      have len : row.length = all.length := by simp [row]
      have take : (row ++ tail).take all.length = row := by simpa only [len] using (splitBlock row tail).1
      have drop : (row ++ tail).drop all.length = tail := by simpa only [len] using (splitBlock row tail).2
      change ((row ++ tail).take all.length).all notLess ::
        flags all.length chosen.length ((row ++ tail).drop all.length) =
          decide (u = C) :: chosen.map (fun v => decide (v = C))
      rw [take,drop,rowFlag all C u (present u List.mem_cons_self) hc upper]
      exact congrArg (List.cons (decide (u = C)))
        (ih (fun v hv => present v (List.mem_cons_of_mem _ hv)))

theorem exactNumericMaximumFlags : ExactNumericMaximumFlags := by
  intro ls vs len C max
  obtain ⟨existsMax,dominates⟩ := List.max?_eq_some_iff.mp max
  change flags ls.length ls.length (numericVector vs) = _
  rw [← len]
  exact flagsBlock vs vs C (fun _ h => h) existsMax dominates

end LogicLineages.PermittedControl.ActualFullValueMaximalMetadata
