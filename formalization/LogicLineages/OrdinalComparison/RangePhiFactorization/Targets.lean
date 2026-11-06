module
public import LogicLineages.OrdinalComparison.RangePhiFactorization.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePhiFactorization.Targets
open PolynomialGraphCompletion WordGuardCompletion

/-- Only the signed index changes, with admission preserved for the literal
source grammar, including arbitrary unused fields on V letters. -/
def PredecessorHeadSyntax : Prop := ∀ D a, LetterAllowed D a → RangeHead a →
  LetterAllowed D (predecessorHead a) ∧
  (predecessorHead a).1 = a.1 ∧ (predecessorHead a).2.1 = a.2.1 ∧
  (predecessorHead a).2.2.1 = a.2.2.1 ∧ (predecessorHead a).2.2.2 = a.2.2.2-1

/-- Source V/X semantics on proved positive-depth domains. The predecessor
has positive depth too: no extrapolation through zero or negative depth. -/
def HeadFactorization : Prop := ∀ D a t, LetterAllowed D a → RangeHead a →
  factorTail a ≤ t → LetterDomain a t ∧ LetterDomain (predecessorHead a) t ∧
  letterValue a t = Phi (letterValue (predecessorHead a) t)

/-- Replacement inside any literal word context. Both original and replacement
complete domains are conclusions, and the original raw argument is shared. -/
def ContextFactorization : Prop := ∀ D : Nat, ∀ A S : Word, ∀ a : Letter,
  WordAllowed D A → WordAllowed D S → LetterAllowed D a → RangeHead a →
  ∀ x : Nat, contextTail A a S ≤ x →
  WordAllowed D (A ++ [predecessorHead a,phiLetter] ++ S) ∧
  WordDomain (A ++ [a] ++ S) x ∧ WordDomain (A ++ [predecessorHead a,phiLetter] ++ S) x ∧
  wordValue (A ++ [a] ++ S) x = wordValue (A ++ [predecessorHead a,phiLetter] ++ S) x

/-- Cancel a Phi head against a coherent V/X head without inventing a fresh
input. All three comparisons reduce exactly to the original interior words. -/
def PhiHeadCancellation : Prop := ∀ D : Nat, ∀ A B : Word, ∀ a : Letter,
  WordAllowed D A → WordAllowed D B → LetterAllowed D a → RangeHead a →
  ∀ x y : Nat, cancellationTail A B a ≤ x → cancellationTail A B a ≤ y →
  WordDomain (A ++ [phiLetter]) x ∧ WordDomain (B ++ [a]) y ∧
  WordAllowed D (B ++ [predecessorHead a]) ∧ WordDomain (B ++ [predecessorHead a]) y ∧
  (wordValue (A ++ [phiLetter]) x < wordValue (B ++ [a]) y ↔
    wordValue A x < wordValue (B ++ [predecessorHead a]) y) ∧
  (wordValue (A ++ [phiLetter]) x = wordValue (B ++ [a]) y ↔
    wordValue A x = wordValue (B ++ [predecessorHead a]) y) ∧
  (wordValue (A ++ [phiLetter]) x ≤ wordValue (B ++ [a]) y ↔
    wordValue A x ≤ wordValue (B ++ [predecessorHead a]) y)

/-- The actual source-code transformation and cutoffs are uniformly primitive
recursive, not just existentially computable bounds. -/
def FactorPrograms : Prop := Primrec predecessorHead ∧ Primrec factorTail ∧
  Primrec (fun p : Word × Letter => wordFactorTail p.1 p.2) ∧
  Primrec (fun p : Word × Letter × Word => contextTail p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Word × Word × Letter => cancellationTail p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.RangePhiFactorization.Targets
