module
public import LogicLineages.PermittedControl.ThickBlockDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

def ThickBlockTailEffective : Prop := Primrec₂ thickBlockTail

/-- Source-general retained thick-block separation. Actual arbitrary phase
states may have different finite tails and any common lower limit suffix r.
No visited top, synchronized hit, residue, survival or comparison is assumed. -/
def ActualThickBlockSeparation : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu P a r A A' : Ordinal.{0}) (R q t : Nat),
  mu < epsilonZero → nu < epsilonZero → P < epsilonZero → a < epsilonZero →
  A < epsilonZero → A' < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → (nu=0 ∨ Order.IsSuccLimit nu) →
  (2 : Ordinal) ≤ a → Ordinal.omega0^a ∣ P →
  r < Ordinal.omega0^a → (r=0 ∨ Order.IsSuccLimit r) →
  20 ≤ R → actualOrdinalNorm mu ≤ R → actualOrdinalNorm nu ≤ R → actualOrdinalNorm a ≤ R →
  R+2 < q → thickBlockTail R B ≤ t →
  actualLimitPart A = mu+(thickBlock P a q+r) →
  actualLimitPart A' = nu+(thickBlock P a q+r) →
  actualOrdinalNorm A = t → actualOrdinalNorm A' = t →
  relativeProfile mu (Ordinal.log Ordinal.omega0 (thickBlock P a q)) <
    relativeProfile nu (Ordinal.log Ordinal.omega0 (thickBlock P a q)) →
  ∃ i : Nat,
    actualLimitPart ((descentWith f)^[i] A-mu) ≠
      actualLimitPart ((descentWith f)^[i] A'-nu) ∧
    thickBlock P a (q-2) ≤ actualLimitPart ((descentWith f)^[i] A-mu) ∧
    thickBlock P a (q-2) ≤ actualLimitPart ((descentWith f)^[i] A'-nu)

/-- Whole source thick-block packet including the computed sufficient tail. -/
def FullThickBlock : Prop := ThickBlockTailEffective ∧ ActualThickBlockSeparation

end LogicLineages.PermittedControl.Targets
