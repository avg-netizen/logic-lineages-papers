module
public import LogicLineages.PermittedControl.CountTransferTargets
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets
public import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountLeadingError
open OrdinalComparison FieldComparison PreparedProjection
open Targets (countCoreConstant)

/-- Recover the original full leading value and the signed error from
one actual count read at its original raw coordinate. The prefix is
allowed to be an identity, so the genuine first-entry index can be zero. -/
def ExactActualCountLeadingError : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (rank : Nat) (lam mu : NONote) (value : Nat),
    LongField (.entry 0 lam mu) →
    max (actualOrdinalNorm lam.1.repr) (actualOrdinalNorm mu.1.repr + 3) ≤ ρ rank →
    LowerOperandActual f ρ (.count rank lam mu) value →
    let x := ρ rank
    let A := countInitial lam.1.repr x
    let η := mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0})
    η ≤ lam.1.repr ∧
    ∃ i : Nat, FirstEntry f A η i ∧
      let q := entryNormAt f A i
      let C := f q
      let κ := countCoreConstant mu.1.repr
      q = f^[i] x ∧ x + i ≤ q ∧ f x ≤ C ∧ q ≤ Nat.log2 C ∧
      2 * (value : Int) = (C : Int) + 2 * ((i : Int) + κ) ∧
      (((i : Int) + κ).natAbs ≤ Nat.log2 C + κ.natAbs) ∧
      ∀ D : Nat, C ≤ D → ((i : Int) + κ).natAbs ≤ Nat.log2 D + κ.natAbs

end LogicLineages.PermittedControl.ActualCountLeadingError
