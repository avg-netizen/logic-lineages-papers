module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullTargets
public import Mathlib.Logic.Function.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
open CircuitLinear Narendran

theorem slot_index_injective (n g : Nat) : Function.Injective (@slotIndex n g) := by
  intro a b h
  cases a <;> cases b <;>
    simp only [slotIndex,polynomialAux,constantAux,scalarCount] at h
  all_goals first
    | { congr 1 <;> apply Fin.ext <;> omega }
    | omega

theorem slot_index_bound (n g : Nat) (s : Slot n g) : slotIndex s<unknownCount n g := by
  cases s <;> simp only [slotIndex,unknownCount,constantAux,polynomialAux,scalarCount] <;> omega

theorem exact_allocation : Targets.ExactAllocation :=
  fun n g => ⟨slot_index_injective n g,slot_index_bound n g⟩

/-- Every slot in the constant-forced prefix is an original wire, input slack,
or one of the four reserved scalar gate slots. No polynomial witness occurs. -/
theorem scalar_slots_cover (n g j : Nat) (hj : j<scalarCount n g) :
    (∃ i : Fin (n+g), slotIndex (Slot.wire i : Slot n g)=j) ∨
    (∃ i : Fin n, slotIndex (Slot.slack i : Slot n g)=j) ∨
    ∃ (i : Fin g) (k : Fin 4), slotIndex (Slot.scalar i k : Slot n g)=j := by
  by_cases hw : j<n+g
  · exact Or.inl ⟨⟨j,hw⟩,rfl⟩
  · by_cases hs : j<(n+g)+n
    · exact Or.inr (Or.inl ⟨⟨j-(n+g),by omega⟩,by simp only [slotIndex];omega⟩)
    · let t := j-((n+g)+n)
      have ht : t<4*g := by unfold t scalarCount at *;omega
      refine Or.inr (Or.inr ⟨⟨t/4,by omega⟩,⟨t%4,by omega⟩,?_⟩)
      simp only [slotIndex]
      unfold t
      omega

/-- A single global assignment extends the values of disjoint literal slots.
The default outside the declared block is irrelevant; no occurrence is renamed. -/
noncomputable def allocate {n g : Nat} (values : Slot n g → NPolynomial) : Nat → NPolynomial :=
  Function.extend slotIndex values (fun _ => 0)

theorem allocate_at {n g : Nat} (values : Slot n g → NPolynomial) (s : Slot n g) :
    allocate values (slotIndex s)=values s :=
  (slot_index_injective n g).extend_apply values (fun _ => 0) s

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
