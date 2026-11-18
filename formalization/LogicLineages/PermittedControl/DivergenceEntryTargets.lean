module
public import LogicLineages.PermittedControl.TerminalPhaseTargets

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- An actual oriented divergence at a common clock forces strict final entry
order. All future budgets and original-clock non-entry must be derived. -/
def ActualDivergenceEntryOrder : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu A A' : Ordinal.{0}) (i t : Nat),
  mu < epsilonZero → nu < epsilonZero → A < epsilonZero → A' < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → (nu=0 ∨ Order.IsSuccLimit nu) →
  actualOrdinalNorm ((descentWith f)^[i] A)=t →
  actualOrdinalNorm ((descentWith f)^[i] A')=t →
  actualOrdinalNorm mu ≤ t → actualOrdinalNorm nu ≤ t →
  0 < actualLimitPart ((descentWith f)^[i] A-mu) →
  actualLimitPart ((descentWith f)^[i] A-mu) < actualLimitPart ((descentWith f)^[i] A'-nu) →
  ∃ tau sigma : Nat, i < tau ∧ tau < sigma ∧
    FirstEntry f A mu tau ∧ FirstEntry f A' nu sigma ∧
    entryNormAt f A tau=f^[tau-i] t ∧ entryNormAt f A' sigma=f^[sigma-i] t ∧
    entryNormAt f A tau < entryNormAt f A' sigma

end LogicLineages.PermittedControl.Targets
