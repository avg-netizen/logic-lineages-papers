module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion
open PolynomialGraphCompletion WordGuardCompletion

/-- A literal non-shift occurrence, rather than a semantic growth assumption. -/
def Nonlinear (w : Word) : Prop := ∃ a ∈ w, a.1 ≠ 0

/-- One extra exponent step absorbs the full possible signed-shift loss. -/
def growthOffset (w : Word) : Nat := wordOffset w + 1

def growthTail (w : Word) : Nat := wordTail w + 2 * wordOffset w + 2

/-- The second bound makes the exponential dominate the larger raw input
plus the absolute signed offset of the opposite leaf. -/
def terminalTail (w : Word) (b : Int) : Nat :=
  max (growthTail w) (2 * growthOffset w + b.natAbs + 2)

end LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion
