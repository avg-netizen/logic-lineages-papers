module
public import LogicLineages.PermittedControl.CountCongruenceNamedRowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.CountCongruenceNamedRow
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

/-- Corrected pointwise comparator: valuation agreement guards the entire
evaluation equivalence. Original CountCongruenceNamedRow.ActualNamedRow is
retained unchanged as the failed historical target. -/
def ActualNamedRowGuarded : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m rank : Nat) (lam mu : NONote) (c u v : Int) (ρ : Nat → Nat),
    0 < m → ProperField (.entry 0 lam mu) →
    let x := ρ rank
    tailCode B (rawNoteEncode lam.1) (rawNoteEncode mu.1) m ≤ x →
    let p := row m (shortGapLength lam mu) (actualOrdinalNorm mu.1.repr) c u v
    ∃ i : Nat,
      FirstEntry f (countInitial lam.1.repr x) mu.1.repr i ∧
      ClosedOrdinaryValueDomain (.entry 0 lam mu) x ∧
      LowerOperandActual f ρ (.count rank lam mu) i ∧
      lowerOperandRead f ρ (.count rank lam mu) = some (some i) ∧
      (∀ ν : Nat → Nat, ν 1 = x →
        (p.eval ν ↔ (m : Int) ∣ c + u * (x : Int) + v * (i : Int)))

end LogicLineages.PermittedControl.CountCongruenceNamedRow
