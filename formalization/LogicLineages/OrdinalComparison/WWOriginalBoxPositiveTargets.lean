module
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleAssignment

/-- Genuine original C-grading of the positive-coordinate box recursion. -/
def OriginalBoxPositiveGrade : Prop :=
  ∀ (Γ : List Ty) (m n : Nat), n < m →
    ∀ (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
      (∀ j, AmbientGrade Γ j.val (f j)) →
      (∀ j, AmbientGrade Γ j.val (g j)) →
      ∀ i : Nat, 0 < i → i ≤ m →
        AmbientGrade Γ i (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i)

/-- Exact original F2 numeric bound on every positive box coordinate.
The input budgets are arbitrary positive-sum numeric majorants, not assumed
output estimates or a redefined control. Original bounded C-vectors supply
these budgets by their scalar coordinates. -/
def OriginalBoxPositiveNorm : Prop :=
  ∀ (Γ : List Ty) (m n : Nat), n < m →
    ∀ (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
      (ρ : AdmissibleSubstitution Γ) (A B : Nat), 0 < A + B →
      (∀ j, actualOrdinalNorm (expressionValue ρ (f j)) ≤ A) →
      (∀ j, actualOrdinalNorm (expressionValue ρ (g j)) ≤ B) →
      ∀ i : Nat, 0 < i → i ≤ m →
        actualOrdinalNorm (expressionValue ρ
          (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i)) ≤
            fastControl 2 (A + B + n)

end LogicLineages.OrdinalComparison.Source.Targets
