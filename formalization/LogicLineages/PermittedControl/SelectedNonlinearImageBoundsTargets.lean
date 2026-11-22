module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedNonlinearImageBounds
open OrdinalComparison FieldComparison

/-- A bare raw coordinate is linear. A positive iterate and a proper
entry field belong to the original nonlinear full-value comparison. -/
def NonlinearField : ValueField → Prop
  | .iterate a => 0 < a
  | .entry _ _ _ => True

def OrdinaryFullValueImage : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (F : ValueField) (x value : Nat), NonlinearField F → ClosedOrdinaryValueDomain F x →
    FieldValue f F x value → ∃ q : Nat, x ≤ q ∧ value = f q

/-- The actual prefix may hit at index zero, as in the source identity
convention. The original first-entry count and endpoint are retained. -/
def ActualPrefixErrorBound : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lam target : NONote) (x i : Nat), Order.IsSuccLimit lam.1.repr →
    (target.1.repr = 0 ∨ Order.IsSuccLimit target.1.repr) →
    target.1.repr ≤ lam.1.repr → actualOrdinalNorm lam.1.repr ≤ x →
    FirstEntry f (countInitial lam.1.repr x) target.1.repr i →
    let q := entryNormAt f (countInitial lam.1.repr x) i
    q = f^[i] x ∧ x + i ≤ q ∧ f x ≤ f q ∧ q ≤ Nat.log2 (f q)

def DistinctFullValueSeparation : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ p q : Nat, f p < f q → f p ≤ Nat.log2 (f q)

def RawCoordinateLogBound : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (z C : Nat), f z ≤ C → z ≤ Nat.log2 C

def FullSelectedNonlinearImageBounds : Prop :=
  OrdinaryFullValueImage ∧ ActualPrefixErrorBound ∧
  DistinctFullValueSeparation ∧ RawCoordinateLogBound

end LogicLineages.PermittedControl.SelectedNonlinearImageBounds
