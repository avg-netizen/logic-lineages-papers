module
public import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixTargets
import LogicLineages.PermittedControl.AffineCollapseGuardRowsReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPlainTerminalMatrix
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (Snapshot actualRows)
open SignedRowSliceValue (valueAt)

private theorem exactPlainListSum (θ : Nat → Nat) (ts : List (Int × NormalForm.Summand))
    (plain : ∀ s ∈ ts, ∃ i : Nat, s.2 = .variable i) :
    (ts.map (fun s => s.1 * (θ s.2.name : Int))).sum =
      (ts.map (fun s => s.1 * (s.2.term.value θ : Int))).sum := by
  induction ts with
  | nil => rfl
  | cons s ts ih =>
      have h₁ := plain s List.mem_cons_self
      have h₂ := ih (fun t ht => plain t (List.mem_cons_of_mem _ ht))
      obtain ⟨i,hi⟩ := h₁
      simp only [List.map_cons,List.sum_cons]
      rw [h₂]
      simp only [hi,NormalForm.Summand.name,NormalForm.Summand.term,Term.value]

private theorem atomValue (f θ : Nat → Nat) (a : NormalForm.Atom)
    (plain : ∀ s ∈ a.row.2, ∃ i : Nat, s.2 = .variable i) (v : Int) :
    valueAt f θ (atomRow a).2.1 (atomRow a).2.2 v ↔ NormalForm.rowValue a.row θ = v := by
  let ts := a.row.2.map (fun s => (s.1,s.2.name))
  have h := AffineCollapseGuardRows.coordinatesSum f θ ts a.row.1 v
  simpa only [ts,List.map_map,Function.comp_def,atomRow,
    NormalForm.rowValue,exactPlainListSum θ a.row.2 plain] using h

private theorem atomAdmitted (a : NormalForm.Atom) : (atomTest a).Admitted := by
  cases a with
  | nonnegative r => trivial
  | divisible m r => exact Nat.succ_pos m

private theorem atomPolarity (θ : Nat → Nat) (a : NormalForm.Atom) (b : Bool) :
    (atomTest a).atPolarity b (NormalForm.rowValue a.row θ) ↔ b = atomAnswer θ a := by
  have calibrate (P : Prop) [Decidable P] :
      (if b then P else ¬ P) ↔ b = decide P := by
    cases b <;> by_cases h : P <;> simp [h]
  cases a with
  | nonnegative r =>
      exact calibrate (0 ≤ NormalForm.rowValue r θ)
  | divisible m r =>
      change (if b then ((m + 1 : Nat) : Int) ∣ NormalForm.rowValue r θ
        else ¬ ((m + 1 : Nat) : Int) ∣ NormalForm.rowValue r θ) ↔
          b = decide (NormalForm.rowValue r θ % ((m + 1 : Nat) : Int) = 0)
      rw [Int.dvd_iff_emod_eq_zero]
      exact calibrate _

theorem exactPlainTerminalSnapshot : ExactPlainTerminalSnapshot := by
  intro f θ p
  change (∀ a ∈ LinearRows.atoms p, ∀ s ∈ a.row.2, ∃ i : Nat, s.2 = .variable i) →
    ∀ values : Snapshot, actualRows f θ ((LinearRows.atoms p).map atomRow) values ↔
      values = (LinearRows.atoms p).map (fun a => (NormalForm.rowValue a.row θ,atomAnswer θ a))
  generalize LinearRows.atoms p = atoms
  induction atoms with
  | nil =>
      intro _ values
      cases values <;> simp [actualRows]
  | cons a atoms ih =>
      intro plain values
      have head := plain a List.mem_cons_self
      have rest := ih (fun t ht => plain t (List.mem_cons_of_mem _ ht))
      cases values with
      | nil => simp [actualRows]
      | cons v values =>
          change ((atomTest a).Admitted ∧ valueAt f θ (atomRow a).2.1 (atomRow a).2.2 v.1 ∧
            (atomTest a).atPolarity v.2 v.1 ∧ actualRows f θ (atoms.map atomRow) values) ↔
              v :: values = (NormalForm.rowValue a.row θ,atomAnswer θ a) ::
                atoms.map (fun a => (NormalForm.rowValue a.row θ,atomAnswer θ a))
          constructor
          · rintro ⟨_,hv,hb,hs⟩
            have h₁ := (atomValue f θ a head v.1).mp hv
            rw [← h₁] at hb
            have hhead : v = (NormalForm.rowValue a.row θ,atomAnswer θ a) :=
              Prod.ext h₁.symm ((atomPolarity θ a v.2).mp hb)
            rw [hhead,(rest values).mp hs]
          · intro h
            obtain ⟨h₁,h₂⟩ := List.cons.inj h
            subst v
            exact ⟨atomAdmitted a,(atomValue f θ a head _).mpr rfl,
              (atomPolarity θ a _).mpr rfl,(rest values).mpr h₂⟩

end LogicLineages.PermittedControl.OriginalPlainTerminalMatrix
