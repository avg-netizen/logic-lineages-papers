module
public import LogicLineages.OrdinalComparison.PeakOrbitDefinitions

@[expose] public section

/-! Exact actual-source statements for paper07 lem:sparse and lem:roots,
paper.tex lines119–166. All endpoints/counts are the independent well-founded
actual-ordinal evaluator; no abstract peak oracle is supplied. Root means
outside the literal fixed Phi range, not a decidable surrogate. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualSparsePeaks : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Ordinal.omega0 ≤ a →
    2 ≤ actualOrdinalNorm a →
    let L := actualReplacementCount a
    let s := (Phi^[L - 1]) (actualOrdinalNorm a)
    let Z := actualTerminalValue a
    0 < L ∧ L ≤ s - 1 ∧ Z = Phi s ∧
      Z < actualCollapse a ∧ actualCollapse a = Z + L ∧
      actualCollapse a < 2 * Z ∧ 2 * Z < Phi (s + 1) ∧
      ∀ u : Nat, u < s → Phi u ≤ Phi (s - 1)

def ControlRootOrbitCancellation : Prop :=
  ∀ t u L J : Nat, ControlRoot t → ControlRoot u →
    (Phi^[L]) t = (Phi^[J]) u → L = J ∧ t = u

def ActualRootPeakInjectivity : Prop :=
  ∀ a b : Ordinal.{0}, a < epsilonZero → b < epsilonZero →
    Ordinal.omega0 ≤ a → Ordinal.omega0 ≤ b →
    ControlRoot (actualOrdinalNorm a) → ControlRoot (actualOrdinalNorm b) →
    actualTerminalValue a = actualTerminalValue b → a = b

end LogicLineages.OrdinalComparison.Targets
