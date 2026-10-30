module
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:successor, paper.tex658–682, actual maximum identity (7.3).
Every budget is retained, including a zero leading coefficient. This supplier
alone does not identify complete suffix-kernel traces or their counts. -/
def ActualSuccessorPrincipalWeight : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma →
    Ordinal.omega0 ^ gamma * Ordinal.omega0 < epsilonZero →
      0 < actualOrdinalNorm (Ordinal.omega0 ^ gamma)

def ActualSuccessorPrincipalMaximum : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma →
    Ordinal.omega0 ^ gamma * Ordinal.omega0 < epsilonZero → ∀ b : Nat,
      let theta := Ordinal.omega0 ^ gamma
      let w := actualOrdinalNorm theta
      actualMaximumPredecessor (theta * Ordinal.omega0) b =
        theta * ((b / w : Nat) : Ordinal) + actualMaximumPredecessor theta (b % w)

def ActualSuccessorPrincipalMaximumShift : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma →
    Ordinal.omega0 ^ gamma * Ordinal.omega0 < epsilonZero → ∀ b : Nat,
      actualOrdinalNorm (Ordinal.omega0 ^ gamma) ≤ b →
      actualMaximumPredecessor (Ordinal.omega0 ^ gamma * Ordinal.omega0) b =
        Ordinal.omega0 ^ gamma +
          actualMaximumPredecessor (Ordinal.omega0 ^ gamma * Ordinal.omega0)
            (b - actualOrdinalNorm (Ordinal.omega0 ^ gamma))

end LogicLineages.OrdinalComparison.Targets
