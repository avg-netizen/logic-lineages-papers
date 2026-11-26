module
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual synchronized processing of a common finite omega-tail above a fixed
positive-limit retained prefix. Includes k=0, covers generated quadratic tails
and original nonsensitive units, and asserts true first hits and norm orbits.
The affordability premises are explicit supporting bounds, later discharged
from the original-unit common tail. They are not a supplied hit or count. -/
def ActualLinearReturn : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu P A A' : Ordinal.{0}) (k t : Nat),
  mu < epsilonZero → nu < epsilonZero → P < epsilonZero →
  A < epsilonZero → A' < epsilonZero → Order.IsSuccLimit P →
  actualLimitPart A=mu+(P+Ordinal.omega0*(k : Ordinal)) →
  actualLimitPart A'=nu+(P+Ordinal.omega0*(k : Ordinal)) →
  actualOrdinalNorm A=t → actualOrdinalNorm A'=t →
  max 2 (max (actualOrdinalNorm (mu+(P+Ordinal.omega0*(k : Ordinal))))
    (max (actualOrdinalNorm (nu+(P+Ordinal.omega0*(k : Ordinal))))
      (max (actualOrdinalNorm (mu+P)+3) (actualOrdinalNorm (nu+P)+3)))) ≤ t →
  FirstEntry f A (mu+P) k ∧ FirstEntry f A' (nu+P) k ∧
  actualOrdinalNorm ((descentWith f)^[k] A)=f^[k] t ∧
  actualOrdinalNorm ((descentWith f)^[k] A')=f^[k] t ∧
  actualLimitPart ((descentWith f)^[k] A-mu)=P ∧
  actualLimitPart ((descentWith f)^[k] A'-nu)=P

end LogicLineages.PermittedControl.Targets
