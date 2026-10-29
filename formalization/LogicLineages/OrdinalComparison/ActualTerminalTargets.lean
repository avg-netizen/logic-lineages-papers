module
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section

/-! Independent evaluator and full terminal-decomposition specifications.
Paper 05, `cor:closed-evaluation` and `thm:complete-count`, lines 233–263.
The first-finite path target concerns the literal sequence of actual nonfinite
replacements. The complete-count statement retains the source lambda/t domain,
positive count, Phi iteration, value decomposition and both strict bounds.
No encoded Computable theorem is asserted; that part of closed evaluation
remains a separate obligation. No candidate terminal-property proof is imported.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualTerminalRecursion : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    (a < Ordinal.omega0 → actualTerminalData a = (a.card.toNat, 0)) ∧
    (Ordinal.omega0 ≤ a → actualTerminalData a =
      (actualTerminalValue (actualDescentStep a), actualReplacementCount (actualDescentStep a) + 1))

def ActualTerminalFirstFinite : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    (actualDescentStep^[actualReplacementCount a]) a = (actualTerminalValue a : Ordinal) ∧
    ∀ k : Nat, k < actualReplacementCount a → Ordinal.omega0 ≤ (actualDescentStep^[k]) a

def ActualTerminalValueIdentities : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    actualCollapse a = actualTerminalValue a + actualReplacementCount a ∧
    actualTerminalValue a = (Phi^[actualReplacementCount a]) (actualOrdinalNorm a)

def ActualCompleteTerminalDecomposition : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a →
    ∀ t : Nat, actualOrdinalNorm a ≤ t →
      let initial := a + ((t - actualOrdinalNorm a : Nat) : Ordinal)
      actualCollapse initial = actualTerminalValue initial + actualReplacementCount initial ∧
      actualTerminalValue initial = (Phi^[actualReplacementCount initial]) t ∧
      0 < actualReplacementCount initial ∧
      actualTerminalValue initial < actualCollapse initial ∧
      actualCollapse initial < 2 * actualTerminalValue initial

end LogicLineages.OrdinalComparison.Targets
