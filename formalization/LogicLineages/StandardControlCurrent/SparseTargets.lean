module
public import LogicLineages.OrdinalComparison.PeakOrbitDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.SparseTargets
open OrdinalComparison

/-- Current paper18 u:lem:sparse, over actual ordinals and the literal fixed
standard F5(n+100). Count is the actual number of nonfinite replacements;
terminal is the independently recursively defined first finite value. No
selected-control, abstract peak, computability, or notation-domain substitute. -/
def SparsePeaks : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Ordinal.omega0 ≤ a →
    2 ≤ actualOrdinalNorm a →
    let L := actualReplacementCount a
    let s := (Phi^[L - 1]) (actualOrdinalNorm a)
    let Z := actualTerminalValue a
    0 < L ∧ L ≤ s - 1 ∧ Z = Phi s ∧
      Z < actualCollapse a ∧ actualCollapse a = Z + L ∧
      actualCollapse a < 2 * Z ∧ 2 * Z < Phi (s + 1) ∧
      ∀ u : Nat, u < s → Phi u ≤ Phi (s - 1)

end LogicLineages.StandardControlCurrent.SparseTargets
