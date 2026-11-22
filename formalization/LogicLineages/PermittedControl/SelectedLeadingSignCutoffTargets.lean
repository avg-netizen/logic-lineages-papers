module
public import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedLeadingSignCutoff

/-- An effective bound on the greatest original raw coordinate. -/
def cutoff (K K₀ : Nat) : Nat := 4 * (K + K₀ + 2)

def CutoffEffective : Prop := Primrec₂ cutoff

def AbsoluteErrorBelowHalf : Prop :=
  ∀ (K K₀ C : Nat), cutoff K K₀ ≤ Nat.log2 C →
    2 * (K * Nat.log2 C + K₀) < C

/-- The source row is doubled to keep its half-integral leading
coefficient exact. The paid decomposition and logarithmic coefficient
bound are the original inputs of this final sign test. -/
def ActualLeadingSign : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (z C K K₀ : Nat) (L R E : Int),
    cutoff K K₀ ≤ z → f z ≤ C → L ≠ 0 →
    2 * R = L * (C : Int) + 2 * E →
    E.natAbs ≤ K * Nat.log2 C + K₀ →
    (0 < R ↔ 0 < L) ∧ (R < 0 ↔ L < 0) ∧ (0 ≤ R ↔ 0 < L) ∧ R ≠ 0

def FullSelectedLeadingSignCutoff : Prop :=
  CutoffEffective ∧ AbsoluteErrorBelowHalf ∧ ActualLeadingSign

end LogicLineages.PermittedControl.SelectedLeadingSignCutoff
