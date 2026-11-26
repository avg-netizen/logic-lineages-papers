module
public import LogicLineages.PermittedControl.ActualShortCountCleanupTargets
import LogicLineages.PermittedControl.ActualShortCountCleanupCountProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualShortCountCleanup
open PreparedProjection ActualZeroClassReplacement ActualZeroClassOutputState

private theorem sumCons (rd : Read) (rs : List Read) :
    readSum (rd :: rs) = rd.1.1 * (rd.2 : Int) + readSum rs := rfl

private theorem shortReadValue (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (op : LowerOperand) (v : Nat) (actual : LowerOperandActual f ρ op v)
    (short : 0 < shortLength op) : v = shortLength op := by
  cases op with
  | coordinate rank => exact (Nat.lt_irrefl 0 short).elim
  | ordinary rank field => exact (Nat.lt_irrefl 0 short).elim
  | count rank lam mu => exact exactPositiveShortCount f B selected ρ rank lam mu v short actual

private theorem actualAmong (f ρ : Nat → Nat) (xs : List Read) (rd : Read)
    (paid : liftedReads f ρ xs) (among : rd ∈ xs) : LowerOperandActual f ρ rd.1.2 rd.2 := by
  induction xs with
  | nil => cases among
  | cons first rest ih =>
      rcases List.mem_cons.mp among with equal | later
      · subst rd
        exact paid.1
      · exact ih paid.2.2 later

private theorem retainedFacts (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (xs : List Read) (paid : liftedReads f ρ xs) :
    liftedReads f ρ (retained xs) ∧ readSum xs = shortShift xs + readSum (retained xs) := by
  induction xs with
  | nil => exact ⟨True.intro,rfl⟩
  | cons rd xs ih =>
      obtain ⟨a, hit, remainder⟩ := paid
      obtain ⟨afterReads, same⟩ := ih remainder
      by_cases keep : shortLength rd.1.2 = 0
      · have next : retained (rd :: xs) = rd :: retained xs := by simp [retained,keep]
        rw [next]
        refine ⟨⟨a,hit,afterReads⟩,?_⟩
        simp only [sumCons,shortShift,keep,Nat.cast_zero,mul_zero,zero_add]
        rw [same]
        ac_rfl
      · have discard : retained (rd :: xs) = retained xs := by simp [retained,keep]
        have shortValue := shortReadValue f B selected ρ rd.1.2 rd.2 a (Nat.pos_of_ne_zero keep)
        rw [discard]
        refine ⟨afterReads,?_⟩
        simp only [sumCons,shortShift,shortValue]
        rw [same,add_assoc]

theorem exactShortCountCleanup : ExactShortCountCleanup := by
  intro f B selected ρ constant raw before paid
  dsimp only
  obtain ⟨kept,same⟩ := retainedFacts f B selected ρ before paid
  have sub : (retained before).Sublist before := List.filter_sublist
  refine ⟨sub,kept,?_,?_,?_⟩
  · intro rd member
    have keptShape : rd ∈ before ∧ shortLength rd.1.2 = 0 := by
      simpa only [retained,List.mem_filter,decide_eq_true_eq] using member
    exact longOfRetained f ρ rd.1.2 rd.2 (actualAmong f ρ (retained before) rd kept member) keptShape.2
  · intro source rd member
    exact source rd (sub.subset member)
  · rw [same,add_assoc]

theorem fullActualShortCountCleanup : FullActualShortCountCleanup :=
  ⟨exactPositiveShortCount,exactIdentityBoundary,exactShortCountCleanup⟩

end LogicLineages.PermittedControl.ActualShortCountCleanup
