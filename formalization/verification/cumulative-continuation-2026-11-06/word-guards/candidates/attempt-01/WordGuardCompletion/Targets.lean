module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordGuardCompletion.Targets
open PolynomialGraphCompletion

/-- Full literal letter domains, not only the unsigned compiler image. -/
def LetterTailCorrect : Prop := ∀ D a t, LetterAllowed D a → letterTail a ≤ t →
  LetterDomain a t ∧ t ≤ letterValue a t + letterOffset a

/-- All letters, including zero-weight or repeated occurrences when used in rows,
are evaluated at their actual successive inputs. -/
def WordTailCorrect : Prop := ∀ D w t, WordAllowed D w → wordTail w ≤ t →
  WordDomain w t ∧ t ≤ wordValue w t + wordOffset w

/-- Effective cofinality usable to pay any generated head's threshold. -/
def WordReachCorrect : Prop := ∀ D w K t, WordAllowed D w → reachTail w K ≤ t →
  WordDomain w t ∧ K ≤ wordValue w t

/-- Existing original arguments are preserved even when a suffix is introduced. -/
def ComposedDomainCorrect : Prop := ∀ D u v t,
  WordAllowed D u → WordAllowed D v →
  reachTail u (wordTail v) ≤ t →
  WordDomain u t ∧ WordDomain v (wordValue u t) ∧ WordDomain (u ++ v) t

/-- Actual explicit numerical functions, including their total malformed behavior. -/
def TailPrograms : Prop := Primrec letterTail ∧ Primrec letterOffset ∧
  Primrec wordTail ∧ Primrec wordOffset ∧
  Primrec (fun p : Word × Nat => reachTail p.1 p.2)

end LogicLineages.OrdinalComparison.WordGuardCompletion.Targets
