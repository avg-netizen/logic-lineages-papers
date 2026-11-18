module
public import LogicLineages.PermittedControl.RelativeDescentDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- eq:local-phase for an actual retained CNF prefix. Divisibility pays the
unabsorbed-prefix condition; actual profile constancy is not assumed. -/
def RetainedLocalPhase : Prop := ∀ (mu P a : Ordinal.{0}) (b : Nat),
  mu < epsilonZero → P < epsilonZero → a < epsilonZero → 0 < P → 0 < a →
  Ordinal.omega0^a ∣ P → actualOrdinalNorm mu ≤ b →
  relativeProfile mu (Ordinal.log Ordinal.omega0 P) + actualOrdinalNorm P < b →
  relativeMaximum mu (P+Ordinal.omega0^a) b = P +
    actualMaximumPredecessor (Ordinal.omega0^a)
      (b-relativeProfile mu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P)

/-- Source successor-tail formula in its affordable-exponent regime, including
finite a0=0. The source large local budget discharges this threshold later. -/
def SuccessorLocalTail : Prop := ∀ (a0 : Ordinal.{0}) (X : Nat), a0 < epsilonZero →
  1+actualOrdinalNorm a0 ≤ X →
  actualMaximumPredecessor (Ordinal.omega0^(a0+1)) X =
    Ordinal.omega0^a0 * ((X/(1+actualOrdinalNorm a0) : Nat) : Ordinal) +
      actualMaximumPredecessor (Ordinal.omega0^a0) (X%(1+actualOrdinalNorm a0))

/-- Actual nonzero maximum and leading exponent for positive local budgets at
a nonzero limit exponent; strict increase follows saturation, not an oracle. -/
def LimitLocalTail : Prop := ∀ (a : Ordinal.{0}), a < epsilonZero → Order.IsSuccLimit a →
  (∀ X : Nat, 0 < X → 0 < actualMaximumPredecessor (Ordinal.omega0^a) X ∧
    Ordinal.log Ordinal.omega0 (actualMaximumPredecessor (Ordinal.omega0^a) X) =
      actualMaximumPredecessor a (X-1)) ∧
  (∀ X Y : Nat, 0 < X → X < Y →
    Ordinal.log Ordinal.omega0 (actualMaximumPredecessor (Ordinal.omega0^a) X) <
      Ordinal.log Ordinal.omega0 (actualMaximumPredecessor (Ordinal.omega0^a) Y))

/-- Exact source omega-squared coincidence criterion in both directions, for
distinct adequate budgets and either ordering of them. -/
def QuadraticLocalCoincidence : Prop := ∀ X Y : Nat, 2 ≤ X → 2 ≤ Y → X ≠ Y →
  (actualLimitPart (actualMaximumPredecessor (Ordinal.omega0^(2 : Ordinal)) X) =
      actualLimitPart (actualMaximumPredecessor (Ordinal.omega0^(2 : Ordinal)) Y) ↔
    max X Y = min X Y+1 ∧ max X Y%2 = 1)

end LogicLineages.PermittedControl.Targets
