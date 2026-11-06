module
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CanonicalGuardSelector.Targets
open PolynomialGraphCompletion OuterShiftNormalization AdjacentRangeWordGuardCompletion
open GuardChildMeasureCompletion

/-- Canonicalization changes only unused fields; original signed/source
semantics agree on every input, not merely on an eventual companion tail. -/
def CanonicalCalibration : Prop := ∀ D a,
  (LetterAllowed D (canonicalHead a) ↔ LetterAllowed D a) ∧
  IsCanonical (canonicalHead a) ∧ (canonicalHead a).1 = a.1 ∧
  rangeRank (canonicalHead a) = rangeRank a ∧
  ∀ t, letterValue (canonicalHead a) t = letterValue a t ∧
    (LetterDomain (canonicalHead a) t ↔ LetterDomain a t)

def ViewSyntax : Prop := ∀ D w, WordAllowed D w →
  WordAllowed D (viewPrefix w) ∧ LetterAllowed D (viewHead w) ∧
  IsCanonical (viewHead w) ∧ (viewHead w).1 ≠ 0 ∧
  WordAllowed D (preparedWord w) ∧
  (coreWord w ≠ [] → coreWord w = viewPrefix w ++ [rawHead w])

/-- Original domains imply prepared domains. No converse assertion discards
an invalid intermediate shift from the original suffix. -/
def ViewCorrect : Prop := ∀ D w t, WordAllowed D w → WordDomain w t →
  WordDomain (preparedWord w) t ∧ wordValue (preparedWord w) t = wordValue w t

def ViewTailCorrect : Prop := ∀ D w t, WordAllowed D w → WordGuardCompletion.wordTail w ≤ t →
  WordDomain w t ∧ WordDomain (preparedWord w) t ∧ wordValue (preparedWord w) t = wordValue w t

def ViewMeasure : Prop := ∀ D A B, WordAllowed D A → WordAllowed D B →
  wordMeasure D (preparedWord A,preparedWord B) = wordMeasure D (A,B)

def CaseSound : Prop := ∀ D code rev next current, GuardCase D code rev next current →
  1 ≤ code ∧ code ≤ 7 ∧ GuardChild D next current

/-- All canonical nonlinear head pairs are covered, with exact case labels,
orientation, child admission and original signed outer-shift parameters. -/
def LocalSelectionCorrect : Prop := ∀ D A a B b j k,
  WordAllowed D A → LetterAllowed D a → IsCanonical a → a.1 ≠ 0 →
  WordAllowed D B → LetterAllowed D b → IsCanonical b → b.1 ≠ 0 →
  let q := selectHeads A a B b
  GuardCase D q.1 q.2.1 q.2.2 (A++[a,shiftLetter j],B++[b,shiftLetter k]) ∧
  WordAllowed D q.2.2.1 ∧ WordAllowed D q.2.2.2

def SelectionCoverage : Prop := ∀ A B,
  selectWords A B = none ↔ ShiftOnly A ∨ ShiftOnly B

/-- The actual total selector returns an admitted certified child whose
measure decreases relative to the original, unprepared word pair. -/
def SelectedChildCorrect : Prop := ∀ D A B q,
  WordAllowed D A → WordAllowed D B → selectWords A B = some q →
  GuardCase D q.1 q.2.1 q.2.2 (preparedWord A,preparedWord B) ∧
  ChildDecrease D q.2.2 (A,B) ∧ WordAllowed D q.2.2.1 ∧ WordAllowed D q.2.2.2

def SelectorPrograms : Prop := Primrec canonicalHead ∧ Primrec viewPrefix ∧ Primrec rawHead ∧
  Primrec viewHead ∧ Primrec preparedWord ∧
  Primrec (fun p : Word × Letter × Word × Letter => selectHeads p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Word × Word => selectWords p.1 p.2)

end LogicLineages.OrdinalComparison.CanonicalGuardSelector.Targets
