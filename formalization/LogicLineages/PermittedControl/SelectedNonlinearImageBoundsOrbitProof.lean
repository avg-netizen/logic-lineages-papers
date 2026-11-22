module
public import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsTargets
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsGrowthProof
import LogicLineages.PermittedControl.RelativeTrajectoryProof
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.CountProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedNonlinearImageBounds
open OrdinalComparison FieldComparison

theorem actualPrefixErrorBound : ActualPrefixErrorBound := by
  intro f B selected lam target x i limit targetLimit _ affordable hit
  let init := countInitial lam.1.repr x
  let q := entryNormAt f init i
  have initial := count_initial_facts lam.1.repr x (normalRepresentationSound lam) limit affordable
  have hitBound := firstEntry_le_terminal f init target.1.repr initial.1 targetLimit i hit
  have orbit : q = f^[i] x := by
    change actualOrdinalNorm ((descentWith f)^[i] init) = _
    rw [trajectory_norm f init initial.1 i hitBound,initial.2.1]
  have counted : x + i ≤ q := by rw [orbit]; exact orbitGrowth f B selected x i
  have input : x ≤ q := (Nat.le_add_right x i).trans counted
  have increase := (selected_threshold_admissible f B selected).1.monotone input
  exact ⟨orbit,counted,increase,rawCoordinateLogBound f B selected q (f q) le_rfl⟩

private theorem iterateImage (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (x i value : Nat) (positive : 0 < i) (actual : value = f^[i] x) :
    ∃ q : Nat, x ≤ q ∧ value = f q := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt positive)
  refine ⟨f^[j] x,(Nat.le_add_right x j).trans (orbitGrowth f B selected x j),?_⟩
  simpa only [Function.iterate_succ_apply'] using actual

theorem ordinaryFullValueImage : OrdinaryFullValueImage := by
  intro f B selected F x value nonlinear domain actual
  cases F with
  | iterate a =>
    exact iterateImage f B selected x a value nonlinear actual
  | entry a lam mu =>
    obtain ⟨proper,affordable⟩ := domain
    obtain ⟨limit,targetLimit,below⟩ := proper
    obtain ⟨i,hit,result⟩ := actual
    have positive := proper_entry_pos f lam.1.repr mu.1.repr x i limit below hit
    have orbit := (actualPrefixErrorBound f B selected lam mu x i limit targetLimit below.le affordable hit).1
    have complete : value = f^[a+i] x := by
      rw [result,orbit,Function.iterate_add_apply]
    exact iterateImage f B selected x (a+i) value (by omega) complete

end LogicLineages.PermittedControl.SelectedNonlinearImageBounds
