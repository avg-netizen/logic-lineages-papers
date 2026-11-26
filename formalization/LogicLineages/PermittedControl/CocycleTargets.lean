module
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Literal source affordable cocycle, including count addition and actual
norm continuation. No intermediate hit or reset is supplied as a premise. -/
def ActualAffordableCocycle : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu kappa lambda : Ordinal.{0}) (t : Nat),
  mu < epsilonZero → kappa < epsilonZero → lambda < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → Order.IsSuccLimit kappa → Order.IsSuccLimit lambda →
  mu < kappa → kappa < lambda →
  max 2 (max (actualOrdinalNorm lambda) (max (actualOrdinalNorm kappa) (actualOrdinalNorm mu))) ≤ t →
  let A := countInitial lambda t
  ∃ i j k : Nat, FirstEntry f A kappa i ∧
    let h := entryNormAt f A i
    FirstEntry f (countInitial kappa h) mu j ∧ FirstEntry f A mu k ∧
    (descentWith f)^[i] A=countInitial kappa h ∧
    k=i+j ∧ entryNormAt f A k=entryNormAt f (countInitial kappa h) j ∧
    h=f^[i] t ∧ entryNormAt f (countInitial kappa h) j=f^[j] h ∧
    entryNormAt f A k=f^[k] t

end LogicLineages.PermittedControl.Targets
