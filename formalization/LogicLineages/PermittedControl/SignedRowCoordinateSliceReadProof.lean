module
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowCoordinateSlice
open FieldComparison PreparedProjection FiniteStripCollectorRecovery
open MixedSameRankResidue (WeightedOperand)

theorem expectedSelected (f : Nat → Nat) (rank a : Nat) (t : WeightedOperand)
    (same : t.2.rank = rank) :
    expectedRead f rank a (1,t.2) =
      (lowerOperandRead f (fun _ => a) t.2).map (fun r => r.map (fun v => [(1,v)])) := by
  simp [expectedRead,same]

theorem expectedUntouched (f : Nat → Nat) (rank a : Nat) (t : WeightedOperand)
    (different : t.2.rank ≠ rank) : expectedRead f rank a (1,t.2) = some (some []) := by
  simp [expectedRead,different]

theorem sameCoordinateRead (f ρ : Nat → Nat) (rank a : Nat) (op : LowerOperand)
    (same : op.rank = rank) (agree : ρ rank = a) :
    lowerOperandRead f ρ op = lowerOperandRead f (fun _ => a) op := by
  cases op <;> simp only [LowerOperand.rank] at same <;> subst rank <;>
    simp only [lowerOperandRead,agree]

theorem hitRead (f ρ : Nat → Nat) (op : LowerOperand) (v : Nat) :
    lowerOperandRead f ρ op = some (some v) ↔ LowerOperandActual f ρ op v :=
  preparedTiedProjection.1 f ρ op v

private theorem failureStatuses (result : ClosedNaturalFieldResult) (D : Prop) (V : Nat → Prop)
    (invalid : result = none ↔ ¬ D)
    (miss : D → (result = some none ↔ ∀ v, ¬ V v)) :
    (result = none ↔ ¬ D) ∧ (result = some none ↔ D ∧ ∀ v, ¬ (D ∧ V v)) := by
  refine ⟨invalid,?_⟩
  constructor
  · intro missing
    have domain : D := by
      by_contra outside
      have rejected := invalid.mpr outside
      rw [missing] at rejected
      cases rejected
    exact ⟨domain,fun v value => (miss domain).mp missing v value.2⟩
  · rintro ⟨domain,noValue⟩
    exact (miss domain).mpr (fun v value => noValue v ⟨domain,value⟩)

theorem fixedReadFailures (f : Nat → Nat) (a : Nat) (op : LowerOperand) :
    (lowerOperandRead f (fun _ => a) op = none ↔ ¬ sourceDomain a op) ∧
    (lowerOperandRead f (fun _ => a) op = some none ↔ sourceDomain a op ∧
      ∀ v, ¬ LowerOperandActual f (fun _ => a) op v) := by
  cases op with
  | coordinate r =>
    simp only [lowerOperandRead,sourceDomain,LowerOperandActual]
    refine ⟨by simp,?_⟩
    constructor
    · intro h
      cases Option.some.inj h
    · rintro ⟨_,noValue⟩
      exact (noValue a rfl).elim
  | ordinary r F =>
    have spec := closedOrdinaryValueActual f F a
    exact failureStatuses _ _ _ spec.1 (fun h => (spec.2 h).2)
  | count r lam mu =>
    have spec := closedOrdinaryCountActual f lam mu a
    exact failureStatuses _ _ _ spec.1 (fun h => (spec.2 h).2)

end LogicLineages.PermittedControl.SignedRowCoordinateSlice
