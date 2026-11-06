module
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Targets
open PolynomialGraphCompletion WordGuardCompletion

/-- Every admitted nonlinear letter, including the original independently
scheduled counter, has an exponential lower bound at its literal paid tail. -/
def LetterGrowth : Prop := ∀ D a t, LetterAllowed D a → a.1 ≠ 0 →
  letterTail a ≤ t → LetterDomain a t ∧ 2 ^ t ≤ letterValue a t

/-- A stronger bookkeeping form at the existing composed-word tail. -/
def CompensatedGrowth : Prop := ∀ D w t, WordAllowed D w → Nonlinear w →
  wordTail w ≤ t → WordDomain w t ∧
    2 ^ (t - wordOffset w) ≤ wordValue w t + wordOffset w

/-- The source's computed exponential lower bound, on original raw inputs
and actual successive letter domains. -/
def WordGrowth : Prop := ∀ D w t, WordAllowed D w → Nonlinear w →
  growthTail w ≤ t → WordDomain w t ∧
    2 ^ (t - growthOffset w) ≤ wordValue w t

/-- Terminal nonlinear/leaf comparison on the source region y ≤ x. The
same-variable case is included; no fictitious linear atom x < W(x) is emitted. -/
def TerminalGuard : Prop := ∀ D w x y b, WordAllowed D w → Nonlinear w →
  terminalTail w b ≤ x → terminalTail w b ≤ y → y ≤ x →
  WordDomain w x ∧ WordDomain [shiftLetter b] y ∧
    wordValue [shiftLetter b] y < wordValue w x

/-- These are the actual total numerical cutoff functions, without a
hypothesized effectiveness premise or semantic oracle. -/
def GrowthPrograms : Prop := Primrec growthOffset ∧ Primrec growthTail ∧
  Primrec (fun p : Word × Int => terminalTail p.1 p.2)

end LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Targets
