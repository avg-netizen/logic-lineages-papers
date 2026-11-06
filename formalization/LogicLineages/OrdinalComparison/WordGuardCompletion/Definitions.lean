module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordGuardCompletion
open PolynomialGraphCompletion

/-- A deliberately generous effective bound, also defined on malformed letters.
Unused numeric fields are harmlessly overpaid rather than normalized away. -/
def letterTail (a : Letter) : Nat := a.2.2.1 + a.2.1 + a.2.2.2.natAbs + 4
/-- Absolute signed index is an upper bound on the loss at a signed shift.
Nonlinear symbols lose nothing, but the same bound simplifies composition. -/
def letterOffset (a : Letter) : Nat := a.2.2.2.natAbs

def wordOffset (w : Word) : Nat :=
  w.foldr (fun a n => letterOffset a + n) 0

/-- Sum bounds pay the next domain at the dynamically reached argument,
after every possible preceding signed-shift loss. -/
def wordTail (w : Word) : Nat :=
  w.foldr (fun a n => letterTail a + letterOffset a + n) 0

def reachTail (w : Word) (K : Nat) : Nat := wordTail w + wordOffset w + K

end LogicLineages.OrdinalComparison.WordGuardCompletion
