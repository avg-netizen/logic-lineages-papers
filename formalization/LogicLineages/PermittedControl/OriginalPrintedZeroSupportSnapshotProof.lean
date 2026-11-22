module
public import LogicLineages.PermittedControl.OriginalPrintedZeroSupportTargets
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedZeroSupport
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowGuardedTest (Test)
open SignedRowSliceValue (valueAt)

private theorem guard (t : Test) : admitted t = true ↔ t.Admitted := by
  cases t <;> simp [admitted,Test.Admitted]

private theorem truth (t : Test) (x : Int) : bit t x = true ↔ t.Holds x := by
  cases t <;> simp [bit,Test.Holds,Int.dvd_iff_emod_eq_zero]

private theorem polarity (t : Test) (x : Int) (b : Bool) : bit t x = b ↔ t.atPolarity b x := by
  cases b with
  | true => exact truth t x
  | false =>
    have known := truth t x
    change bit t x = false ↔ ¬ t.Holds x
    cases h : bit t x <;> simp_all

private theorem valueEmpty (f ρ : Nat → Nat) (c result : Int) :
    valueAt f ρ c [] result ↔ c = result := by
  constructor
  · rintro ⟨values,reads,same⟩
    cases values with
    | nil => simpa [MixedSameRankResidue.actualSum] using same
    | cons v vs => exact False.elim reads
  · intro same
    exact ⟨[],True.intro,by simpa [MixedSameRankResidue.actualSum] using same⟩

private theorem cellExact (f ρ : Nat → Nat) (r : Row) (v : Int × Bool) :
    closedCell r = some v ↔ r.2.2 = [] ∧ r.1.Admitted ∧ valueAt f ρ r.2.1 r.2.2 v.1 ∧
      r.1.atPolarity v.2 v.1 := by
  rcases r with ⟨test,c,ts⟩
  cases ts with
  | cons t ts =>
    simp [closedCell]
  | nil =>
    rcases v with ⟨x,b⟩
    by_cases admitCheck : admitted test = true
    · have allowed := (guard test).mp admitCheck
      change (if admitted test then some (c,bit test c) else none) = some (x,b) ↔ _
      rw [if_pos admitCheck]
      constructor
      · intro eq
        obtain ⟨hc,hb⟩ := Prod.mk.inj (Option.some.inj eq)
        subst x
        exact ⟨rfl,allowed,(valueEmpty f ρ c c).mpr rfl,(polarity test c b).mp hb⟩
      · rintro ⟨_,_,measured,tested⟩
        have hc := (valueEmpty f ρ c x).mp measured
        subst x
        exact congrArg (fun b => some (c,b)) ((polarity test c b).mpr tested)
    · constructor
      · intro impossible
        have h : (none : Option (Int × Bool)) = some (x,b) := by simpa [closedCell,admitCheck] using impossible
        cases h
      · intro live
        exact False.elim (admitCheck ((guard test).mpr live.2.1))

private theorem closedCons (r : Row) (rs : List Row) (x : Int × Bool) (xs : Snapshot) :
    closedSnapshot (r::rs) = some (x::xs) ↔ closedCell r = some x ∧ closedSnapshot rs = some xs := by
  cases h₁ : closedCell r <;> cases h₂ : closedSnapshot rs <;>
    simp [closedSnapshot,h₁,h₂,bind,pure]

theorem exactClosedActualSnapshot : ExactClosedActualSnapshot := by
  intro f ρ rows
  induction rows with
  | nil =>
    intro snap
    cases snap with
    | nil => exact ⟨fun _ => ⟨fun r h => False.elim (List.not_mem_nil h),True.intro⟩,fun _ => rfl⟩
    | cons v vs => simp [closedSnapshot,actualRows]
  | cons r rs ih =>
    intro snap
    cases snap with
    | nil =>
      cases h₁ : closedCell r <;> cases h₂ : closedSnapshot rs <;>
        simp [closedSnapshot,h₁,h₂,actualRows,bind,pure]
    | cons x xs =>
      constructor
      · intro holds
        obtain ⟨cell,tail⟩ := (closedCons r rs x xs).mp holds
        obtain ⟨present,admitCheck,value,sign⟩ := (cellExact f ρ r x).mp cell
        obtain ⟨empties,actual⟩ := (ih xs).mp tail
        refine ⟨?_,admitCheck,value,sign,actual⟩
        intro row used
        rcases List.mem_cons.mp used with first | rest
        · simpa only [first] using present
        · exact empties row rest
      · rintro ⟨empties,admitCheck,value,sign,actual⟩
        exact (closedCons r rs x xs).mpr
          ⟨(cellExact f ρ r x).mpr ⟨empties r List.mem_cons_self,admitCheck,value,sign⟩,
            (ih xs).mpr ⟨fun row used => empties row (List.mem_cons_of_mem _ used),actual⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedZeroSupport
